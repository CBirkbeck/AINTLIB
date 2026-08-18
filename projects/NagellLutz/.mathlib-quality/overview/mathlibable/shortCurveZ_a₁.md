## /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveZ_a₁`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task note; decl elaborates, proof is `rfl`)
- decl `LutzNagell.LutzNagellTheorem.shortCurveZ_a₁`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:32`
- kind:                      lemma (theorem-kind → Phase 4.5 skipped)
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + A·x + B` over ℤ and its
  base change to ℚ, plus basic rewriting lemmas (coefficients, equation, discriminant). Downstream
  Lutz–Nagell files import this instead of re-expanding `Δ`/`Equation`.

Qualified name VERIFIED from source: `LutzNagell.LutzNagellTheorem.shortCurveZ_a₁`
(namespaces `LutzNagell` → `LutzNagellTheorem`, lemma name `shortCurveZ_a₁`). The parsed guess in the
task header (`LutzNagell.LutzNagellTheorem.shortCurveZ_a₁`) is correct.

Exact source text:
```lean
@[simp] lemma shortCurveZ_a₁ (A B : ℤ) : (shortCurveZ A B).a₁ = 0 := rfl
```
with
```lean
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }
```

---

### Statement (Phase 1)

`shortCurveZ_a₁` states that the `a₁` Weierstrass coefficient of the project-local short curve
`shortCurveZ A B` is zero:

> For all `A B : ℤ`, `(shortCurveZ A B).a₁ = 0`.

Here `shortCurveZ A B : WeierstrassCurve ℤ` is the **project-local** definition
`{ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }`, i.e. the curve `y² = x³ + A·x + B`.
The lemma is the first of five sibling field-accessor `@[simp]` lemmas (`_a₁`…`_a₆`); it asserts the
value of the `a₁` field, which was *defined* to be `0`. Proof: `rfl` (pure structure projection).

Variables (Lean side):
- `A B : ℤ` — the coefficients of the short curve (mathematical role: the linear/constant terms `A`,`B`).

Hypotheses: none.

Conclusion (math): the coefficient `a₁` of `y² = x³ + Ax + B` is `0` — i.e. there is no `a₁·xy` term.
This is true *by definition of short Weierstrass form*.

Conclusion (Lean): `(shortCurveZ A B).a₁ = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a trivial `@[simp]` field-accessor lemma (`rfl`) about a project-local definition; not a new
structure, not a named theorem, not a `## Main results` entry.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rfl`).
One-liner verdict: n/a — kind is `lemma`, not `def`. (The one-liner exemption table is for `def`s; a
`rfl` *lemma* is by nature a one-liner.) Recorded as a note: this is a glue/projection lemma.

This is a **glue lemma** in the skill's technical sense (body `:= rfl`) about the parent
`def shortCurveZ`. Its verdict is governed by the status of that parent definition.

(Sibling precedent: `shortCurveZ_a₂.md`, `shortCurveZ_a₃.md` in this same directory assessed the
exact analogues — the `a₂` and `a₃` accessors of the identical definition — and both landed
**NO-composable-from-mathlib**. This report independently re-runs the protocol for `a₁` and confirms
the same verdict; the only `a₁`-specific wrinkle is noted under Mathlib search below.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | short Weierstrass form `y²=x³+Ax+B`, `a₁/a₂/a₃` zero coefficients, reduced form         | yes  | `a₁ = a₂ = a₃ = 0`; reduced/short Weierstrass form     | Stanford crypto notes, Dummit notes (Northeastern), Fiveable, Fractalyze GitBook — universally standard; reduction needs char ≠ 2,3 via `y ↦ y + (a₁/2)x + a₃/2` |
|  2 | WebSearch (general form)         | Nagell–Lutz theorem, integer points, division polynomials, torsion                     | yes  | Nagell–Lutz: finite-order pts have integer coords, y\|D | the project's overall target (covered in sibling reports) |
|  3 | WebSearch (named-after/aliases)  | "reduced Weierstrass form" / "short form" coefficient `a₁` (the `xy` term)              | yes  | same as #1; `a₁` is the `xy`-coefficient, zero in short | name varies (short / reduced); the *fact* `a₁=0` is by-definition, never a named lemma |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch #1/#3 + direct mathlib source reading)  | n/a  | covered by #1/#3 + Phase 5 mathlib source              | "a₁ = 0 in short form" is folklore/definitional; no source elevates it to a citable result |
|  5 | Local references                 | `.mathlib-quality/references/` for "short Weierstrass" / "Nagell"                       | n/a  | (directory check) — no PDF defines an `a₁`-accessor    | the accessor of a *specific constructor* is not a literature object |
|  6 | nLab                             | "Weierstrass curve" / "elliptic curve" short form                                       | n/a  | nLab treats elliptic curves abstractly; no per-field accessor lemma for a literal curve | not the level nLab works at |
|  7 | nCatLab (categorical)            | —                                                                                      | n/a  | not a categorical concept                              | a structure-field value, no categorical content |
|  8 | Stacks Project (alg geom)        | Weierstrass equation coefficients                                                       | n/a  | Stacks has Weierstrass eqns but not a "the a₁ field of THIS constructor is 0" lemma | such a lemma is an implementation detail, not a Stacks tag |
|  9 | MathOverflow / Math.SE           | short Weierstrass `a₁` coefficient zero                                                 | n/a  | only confirms #1 (definitional)                        | no MO/SE question treats this as nontrivial |
| 10 | recent arXiv (last 5 yrs)        | Nagell–Lutz formalization / Weierstrass group law formal proof                         | yes  | formal-group-law / Selmer-group papers manipulate `aᵢ` directly | formalization papers handle `a_i` fields via `rfl`/`simp`; none ship a named per-constructor accessor lemma |

### Literature summary (Phase 3)

Concept identified as: the **`a₁` coefficient of the short (reduced) Weierstrass form** is `0`.
Sources agree on the standard form: **yes** — short Weierstrass form universally means
`a₁ = a₂ = a₃ = 0`, leaving `y² = x³ + a₄·x + a₆`. The vanishing of `a₁` is precisely what removes the
`xy` cross-term.
Most general standard form: `a₁ = 0` is a *defining property* of the short form, not a theorem with
hypotheses. No source states "the a₁-accessor of a particular curve constructor" as a result — because
it is a definitional unfolding, settled by `rfl`.
Generality dimensions where the literature varies:
  - underlying ring/field: the classical *reduction to* short form needs char ≠ 2 (to kill `a₁` via
    completing the square in `y`); but here the curve is *constructed* with `a₁ := 0` over ℤ, so the
    value is `0` over *any* base — no char hypothesis is even relevant. The lemma is below the level at
    which generality is meaningful.
Disagreement with the literature: none. The lemma is true and trivially so; the literature simply does
not treat per-constructor field accessors as objects worth naming.

---

### Generality analysis — `shortCurveZ_a₁`

Literature-standard form (from Phase 3): "a₁ = 0 for the short Weierstrass form" — a definitional
property, realised in mathlib as the **typeclass** `WeierstrassCurve.IsShortNF` with member
`a₁ : W.a₁ = 0` and the projection theorem `WeierstrassCurve.a₁_of_isShortNF : W.a₁ = 0`.

| # | Parameter / hypothesis | Current Lean form                | Literature-standard / mathlib-idiom form          | Weaker form? | Reason |
|---|------------------------|----------------------------------|----------------------------------------------------|--------------|--------|
| 1 | `A B : ℤ`              | concrete literal curve over ℤ    | `W : WeierstrassCurve R` with `[W.IsShortNF]`      | yes (vacuously) | mathlib already has the general statement via the `IsShortNF` typeclass; the project's lemma is the maximally-special case (one fixed constructor) of `a₁_of_isShortNF` |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the single-constructor specialisation
of mathlib's `a₁_of_isShortNF`. But this does NOT make it a `YES-but-generalise-first`: the general
form already *exists in mathlib*. The project lemma is redundant, not under-general.
Number of weakening opportunities: 1 (drop to `IsShortNF`), but that target is mathlib's, not new.
Cost of restatement: n/a — no restatement is wanted; the right move (if any) is deletion/inlining (see
Phase 7).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | "let X be a foo" → typeclass/instance?                                   | yes (already in mathlib) | use `[(shortCurveZ A B).IsShortNF]` + `a₁_of_isShortNF` | mathlib's whole short-NF API |
|  2 | sequences/metric → filters/topology?                                    | no — no analysis content | — | — |
|  3 | construct → universal-property class?                                   | no — it's a field read | — | — |
|  4 | set+closure-predicate → bundled substructure?                           | no | — | — |
|  5 | vector-space/field-specific → weaken typeclass?                         | no — value is `0` over any ring | — | — |
|  6 | 1-categorical → higher-categorical?                                     | no | — | — |
|  7 | concrete index (ℤ) → arbitrary monoid/group?                            | partially — `a₁ := 0` holds over any base, captured by `IsShortNF` over any `R` | mathlib's `a₁_of_isShortNF` (generic `R`) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it already lives in mathlib** as `IsShortNF` +
`a₁_of_isShortNF`. The project lemma is the concrete shadow of that API. Because the modern idiom is
mathlib's *existing* one, this does NOT push toward `YES-but-generalise-first` (that bucket is for
contributing a better-formed *new* decl). It reinforces `NO`: mathlib's organisation already subsumes
this.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (a `Prop`-valued `rfl` lemma introduces no typeclass-search path and
no new definitional equality beyond the one `rfl` already witnesses).

---

### Mathlib search-status: `shortCurveZ_a₁`

[A] Lean-Finder       "a₁ coefficient zero short Weierstrass"        no direct hit for a per-constructor accessor; the conceptual hit is `IsShortNF`
[B] Loogle            `?W.a₁ = 0` / `WeierstrassCurve.a₁ = 0`        hit: `WeierstrassCurve.a₁_of_isShortNF` (and `a₁_of_isCharNeTwoNF`, char-2/3 NF variants), `variableChange_a₁`
[C] LeanSearch        "a₁ of short normal form Weierstrass curve"    hit: `WeierstrassCurve.IsShortNF`, `a₁_of_isShortNF`
[D] Grep mathlib src  `a₁ = 0 := rfl` ; `a₁ : W.a₁ = 0` ; `IsShortNF` over `Mathlib/AlgebraicGeometry/EllipticCurve/` →
                      `NormalForms.lean:185 class IsShortNF`, `:196 theorem a₁_of_isShortNF : W.a₁ = 0 := IsShortNF.a₁`;
                      NO `…_a₁ = 0 := rfl` for any concrete constructor anywhere in mathlib
[E] Name pattern      grep `shortCurveZ` / `shortCurve_a` in mathlib   no hits — `shortCurveZ` is project-local; the only `…_a₁ = … := rfl` in mathlib is
                      `VariableChange.variableChange_a₁` (accessor of the genuine `C • W` action, not a one-off literal)

`a₁`-specific note: unlike its sibling `a₂_of_isShortNF` (which mathlib marks `@[simp]`,
`NormalForms.lean:198`), mathlib's `a₁_of_isShortNF` (`:196`) and `a₃_of_isShortNF` (`:201`) are NOT
`@[simp]`. This does not affect the verdict — it just means that, when routed through `IsShortNF`,
`a₁ = 0` is a named-rewrite rather than an auto-simp fact. The project's own `@[simp] shortCurveZ_a₁`
provides the simp behaviour locally for the concrete `shortCurveZ` def.

Searched for both:
  - the user's current form (`(shortCurveZ A B).a₁ = 0`) — **not in mathlib**; `shortCurveZ` doesn't exist there.
  - the literature-standard / general form (`a₁ = 0` on a short-NF curve) — **in mathlib** as
    `WeierstrassCurve.a₁_of_isShortNF` (`Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:196`),
    backed by the `IsShortNF` typeclass (`:185`).

Concluded: **building blocks present** — the lemma is a definitional unfolding of the project's own
`shortCurveZ` constructor. The general *statement* exists in mathlib (`a₁_of_isShortNF`), but the exact
lemma is about a project-local def and is discharged by `simp [shortCurveZ]` / `rfl` in one step. Not a
candidate for mathlib (its subject `shortCurveZ` is not a mathlib object); it is a one-call composition
/ definitional unfolding to inline.

Note on the project's mathlib-fork: this project forks
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, and carries duplicated `General*`/`PID*` tracks —
but NONE of that touches this lemma. `shortCurveZ` / `shortCurveZ_a₁` are genuinely new
project-local glue (the def + its five accessors live only in `ShortWeierstrass.lean`); they are not a
fork of any mathlib decl. The relevant mathlib file here is `NormalForms.lean` (the upstream
`IsShortNF` API), which the project does NOT fork — it simply chose a concrete constructor instead.

---

### Call sites — `shortCurveZ_a₁`

Internal use count: **3** (within the project, excluding the declaring file)
External-to-file callers: **2 distinct files** (`GeneralMain.lean`, `Main.lean`)

| Caller file:line                                                       | Usage pattern (one-line excerpt)                                   |
|------------------------------------------------------------------------|--------------------------------------------------------------------|
| projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean:167  | `simp only [curveQ_a₁, curveQ_a₃, shortCurveZ_a₁, shortCurveZ_a₃, …]` |
| projects/NagellLutz/LutzNagell/LutzNagellTheorem/Main.lean:54          | `simp only [shortCurveZ_a₁, shortCurveZ_a₃, zero_mul, add_zero] at hκ` |
| projects/NagellLutz/LutzNagell/LutzNagellTheorem/Main.lean:57          | `simp only [shortCurveZ_a₁, shortCurveZ_a₃, zero_mul, add_zero] at hdvd` |

Inline-derivation grep (was the equivalent re-derived elsewhere without the lemma?): none — every site
uses the `simp` lemma; nobody hand-unfolds `shortCurveZ` for the `a₁` field. (Confirmed: `grep -rn
shortCurveZ_a₁ --include=*.lean` returns exactly the declaration + these 3 sites; the name appears in
no other project.)

Signal: K = 3 internal uses → it IS real local `simp`-API. But every use is inside a `simp only` set
where `simp [shortCurveZ]` (unfolding the def directly) would serve identically — the lemma is a
convenience handle for the structure projection, not load-bearing mathematics. Per the call-sites
table, K ≥ 3 leans YES *only* when the subject could go to mathlib; here the subject cannot, so the
K-count merely tells us how many sites to update if the lemma is inlined/folded into the def's `simp`
set.

---

### Composition check (Phase 6)

Can `shortCurveZ_a₁` be derived from mathlib (or trivially) in ≤3 chained calls?

Attempt 1: `rfl` — succeeds. `(shortCurveZ A B).a₁` reduces definitionally to the field literal `0`.
  - Mathlib decls used: none needed (definitional).
  - Result: **succeeds** (0 calls).

Attempt 2 (idiomatic inline at call sites): `simp [shortCurveZ]` — succeeds; unfolds the local def and
reads the `a₁ := 0` field directly. Equivalent to citing the bundled five accessors but needs no
separate lemma.
  - Result: **succeeds** (1 simp call).

Attempt 3 (mathlib-routed, if one re-expresses via `IsShortNF`): give `shortCurveZ A B` an `IsShortNF`
instance, then `WeierstrassCurve.a₁_of_isShortNF` gives `a₁ = 0` directly.
  - Mathlib decls used: `WeierstrassCurve.IsShortNF`, `WeierstrassCurve.a₁_of_isShortNF`.
  - Result: **succeeds** (≤2 calls) — overkill here, but shows mathlib already owns the general fact.

Conclusion: **COMPOSABLE** — trivially (`rfl`, or `simp [shortCurveZ]` at each of the 3 sites). No new
lemma is required.

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveZ_a₁`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): "a₁ = 0 in short Weierstrass form" is a *definitional* property (it is
  exactly what removes the `xy` term), never a named result; no source treats a per-constructor field
  accessor as an object.
- Generality analysis (Phase 4): the general statement already exists in mathlib as
  `WeierstrassCurve.a₁_of_isShortNF` (typeclass `IsShortNF`); the project lemma is its single-constructor
  shadow.
- Mathlib search (Phase 5): the user's form is NOT in mathlib (subject `shortCurveZ` is project-local);
  the general form IS (`a₁_of_isShortNF`, `NormalForms.lean:196`). Mathlib deliberately ships no
  `…_a₁ = 0 := rfl` accessor for any concrete curve constructor.
- Composition check (Phase 6): COMPOSABLE — discharged by `rfl` / `simp [shortCurveZ]` in one step.

**Rationale:**

`shortCurveZ_a₁` is a `@[simp]` glue lemma (`:= rfl`) reading off the `a₁` field of the
**project-local** definition `shortCurveZ A B := { a₁ := 0, …, a₄ := A, a₆ := B }`. It cannot go to
mathlib because its subject, `shortCurveZ`, is not a mathlib object — mathlib has no concrete "short
curve over ℤ from (A,B)" constructor, and on purpose: it models the short form by the **`IsShortNF`
typeclass** plus projection theorems like `WeierstrassCurve.a₁_of_isShortNF : W.a₁ = 0`
(`Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:196`). The one place mathlib *does* ship a
`…_a₁ = … := rfl` accessor (`VariableChange.variableChange_a₁`) is for a genuine algebraic operation
`C • W`, not a one-off literal — confirming that per-constructor accessor lemmas are not mathlib's
pattern. The lemma is true and locally convenient (3 call sites), but every use sits inside a
`simp only […]` where `simp [shortCurveZ]` would unfold the definition and read `a₁ = 0` identically;
the building block (the def itself, plus `rfl`) is already present, so the form is a ≤1-call inline,
not a new lemma. This is the canonical NO-composable case: mathlib has the machinery, the exact
statement is a trivial definitional unfolding of a local def, so it belongs at the call site (or as a
local convenience bundle), not in the library.

(It is emphatically NOT `NO-mathlib-has-it`: mathlib does not have *this* statement — it has the more
general `a₁_of_isShortNF` about a *different*, typeclass-bundled subject. And it is NOT
`YES-but-generalise-first`: the more general form already exists in mathlib, so there is nothing new to
contribute by generalising.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks — namely the project's own `def shortCurveZ` (whose `a₁` field is the
literal `0`) and definitional `rfl`; and, at the general level, `WeierstrassCurve.IsShortNF` +
`WeierstrassCurve.a₁_of_isShortNF`. The exact statement is a 0–1-call definitional unfolding.

Mathlib building blocks / local primitives:
- `LutzNagell.LutzNagellTheorem.shortCurveZ` (the local def; field `a₁ := 0`)
- definitional `rfl`
- (general, if ever routed through mathlib) `WeierstrassCurve.IsShortNF`,
  `WeierstrassCurve.a₁_of_isShortNF` — `Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:185,196`

Composition sketch (≤3 lines):
```lean
example (A B : ℤ) : (shortCurveZ A B).a₁ = 0 := rfl
-- or, at each call site, replace `shortCurveZ_a₁` in the simp set with `shortCurveZ`:
--   simp only [shortCurveZ, …] -- unfolds the def, reads a₁ = 0 directly
```

Call sites in our project (from Phase 6.0): **K = 3**
- `GeneralMain.lean:167`, `Main.lean:54`, `Main.lean:57`.

Refactor plan (NOTE — project policy caveat below; do NOT mechanically apply):
At each of the 3 sites, the lemma can be inlined by either (a) leaving the five `shortCurveZ_a*`
accessors as a local convenience bundle (status quo — perfectly fine, and idiomatic), or (b) dropping
them and folding `shortCurveZ` itself into each `simp only […]` set so the def unfolds in place.
Argument flow is unchanged (these are `simp only` rewrite members; swapping `shortCurveZ_a₁` for
`shortCurveZ` unfolds the structure and exposes `a₁ = 0` with no positional-argument concerns).

Next action: **none required for mathlib.** This is a local convenience `simp` lemma about a
project-local definition; it is correctly placed in the project and should NOT be upstreamed. If a
cleaner wants to reduce surface area, the five `shortCurveZ_a*` accessors can be replaced by unfolding
`shortCurveZ` at the 3 call sites — but keeping them as a tidy `@[simp]` accessor bundle is idiomatic
and recommended. Mathlib already owns the general fact via `a₁_of_isShortNF`.

---

## Next step

No mathlib action. Keep `shortCurveZ_a₁` as a project-local `@[simp]` accessor for the local
`shortCurveZ` definition (or optionally inline `simp [shortCurveZ]` at the 3 call sites). The general
statement is already in mathlib as `WeierstrassCurve.a₁_of_isShortNF`; nothing to upstream. Verdict is
consistent with the sibling reports `shortCurveZ_a₂.md` and `shortCurveZ_a₃.md`
(both NO-composable-from-mathlib).
