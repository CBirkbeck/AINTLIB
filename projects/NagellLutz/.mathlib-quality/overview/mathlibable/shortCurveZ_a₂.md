# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveZ_a₂`

> Step-9 single-declaration mathlibability assessment.
> Repo root: `/Users/mcu22seu/Documents/GitHub/aintlib-main`
> Source: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:33`

---

### Baseline (Phase 0)
- lake build:               (not re-run; local build stale per task note — reasoning from source)
- decl `LutzNagell.LutzNagellTheorem.shortCurveZ_a₂`: ✓ resolved at `ShortWeierstrass.lean:33`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  sets up the short Weierstrass curve `y² = x³ + A·x + B` over `ℤ` and its base change to `ℚ`, with basic rewriting lemmas (equation, discriminant).

Exact source line:
```lean
@[simp] lemma shortCurveZ_a₂ (A B : ℤ) : (shortCurveZ A B).a₂ = 0 := rfl
```
where
```lean
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }
```

Qualified name VERIFIED from source: namespaces `LutzNagell` → `LutzNagellTheorem` (lines 19–20),
so the true qualified name is **`LutzNagell.LutzNagellTheorem.shortCurveZ_a₂`**. (The task's
guessed `LutzNagell.LutzNagellTheorem.shortCurveZ_a₂` is correct.)

---

### Statement (Phase 1)

`shortCurveZ_a₂` asserts that the `a₂` Weierstrass coefficient of the project-local short
Weierstrass curve `shortCurveZ A B` equals `0`. Since `shortCurveZ A B` is *defined* by the
structure literal `{ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }`, the statement is the
projection of the literal field value `0` back out of the anonymous constructor — true by
`rfl`. Mathematically: the curve `y² = x³ + A·x + B` has vanishing `a₂` in the general
Weierstrass form `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the coefficients of the short model; no typeclass hypotheses.

Hypotheses (Lean side): none.

Conclusion (math): the `x²`-coefficient `a₂` of the short curve is `0`.
Conclusion (Lean): `(shortCurveZ A B).a₂ = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `rfl` structure-projection helper; not a new structure, not a `## Main
results` entry, not named after a person/place. Pure scaffolding for the Lutz–Nagell proof.

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rfl`).
One-liner verdict: n/a — kind is `lemma`, not `def`. (The 2b def-exemption table applies to
`def`/`abbrev`/`structure`; this is a projection *lemma*. It is recorded here as the trivial
single-line `rfl` it is, which biases the verdict toward a NO bucket exactly as the 2b spirit
intends for one-liners.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

This is a definitional unfolding of one field of a project-local structure literal. There is no
"theorem" here to locate in the literature — the mathematical "content" is the trivial fact that
the short Weierstrass form `y² = x³ + Ax + B` has `a₂ = 0`, which is true by inspection of the
general Weierstrass equation. The literature question reduces to: *is the short Weierstrass model
a standard object, and is "its a₂ is 0" anything a source would state as a result?* The answer to
the first is yes; to the second, no (it is part of the definition of "short form").

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|----------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "short Weierstrass form" "a₂ = 0" coefficient                                            | yes (concept) | short form `y²=x³+Ax+B` ⇔ `a₁=a₂=a₃=0`, `a₄=A`, `a₆=B`        | Silverman AEC III.1; the vanishing of `a₂` is *definitional*, never a named result |
|  2 | WebSearch (general form)         | general Weierstrass equation `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆` reduction to short form        | yes (concept) | over a field with char ≠ 2,3 every curve has a short model with `a₂=0` | the reduction is the result; "a₂=0" is the property *defining* the target form |
|  3 | WebSearch (named-after / aliases)| "depressed cubic" / "short Weierstrass" / "reduced Weierstrass" coefficient a₂           | no (as a lemma) | —                                                                  | no source states "a₂ of the short model is 0" as a lemma; it is a coordinate convention |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback) "Is 'the a₂ coefficient of y²=x³+Ax+B is zero' ever a named lemma, or part of the definition of short Weierstrass form?" | n/a | answered from references/standard knowledge: definitional, not a lemma | reasoned from Silverman; MCP unavailable, fallback used |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                  | n/a  | directory absent                                                     | no references dir for this project — recorded n/a |
|  6 | nLab                             | "Weierstrass equation" / "elliptic curve" short form                                    | no (as a lemma) | nLab has elliptic-curve entries but no "a₂=0" statement             | not a categorical concept; nLab gives the general equation only |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                                                                    | not a categorical concept |
|  8 | Stacks Project                   | Weierstrass equation tag                                                                 | n/a  | Stacks treats Weierstrass models but states no "a₂=0" projection lemma | the short-form coordinate choice is not a Stacks result |
|  9 | MathOverflow / Math.StackExchange| short Weierstrass form coefficients normalization                                        | yes (concept) | confirms short form is the `a₁=a₂=a₃=0` normalization                | discussion-level; nobody states the projection as a lemma |
| 10 | recent arXiv (last 5 years)      | division polynomials / Lutz–Nagell short Weierstrass model                               | no (as a lemma) | papers *use* `y²=x³+Ax+B`; none state its `a₂=0` as a result        | universally a setup convention |

### Literature summary (Phase 3)

Concept identified as: the **short (reduced) Weierstrass form** `y² = x³ + Ax + B`, i.e. the
Weierstrass curve with `a₁ = a₂ = a₃ = 0`, `a₄ = A`, `a₆ = B`.
Sources agree on the standard form: yes — Silverman AEC, Wikipedia, MathOverflow all use the
same normalization.
Most general standard form: the general Weierstrass equation; the short form is the char-≠2,3
specialization. The fact "a₂ = 0" is *part of the definition* of the short form, not a theorem
about it.
Generality dimensions where the literature varies: none relevant — `a₂ = 0` is a coordinate
convention, true by construction for any base ring once one writes the short literal.
Disagreement with the literature: none. The Lean lemma simply re-reads a field set to `0` in a
structure literal.

**Signal:** the literature search returns no *result* matching this declaration — only the
definitional convention. Per the skill, that is a strong indicator the decl is too trivial /
project-specific to be a mathlib contribution in its own right.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the short Weierstrass model is a *definition*; `a₂ = 0`
is one of its defining field equalities.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring `ℤ` (fixed in `shortCurveZ`) | curve over `ℤ` | short form over any commutative ring | yes | `shortCurveZ` hard-codes `ℤ`; a general `WeierstrassCurve.ofShort {R} (A B : R)` would generalize, but the *lemma* `a₂ = 0` would still just be the `@[simps]`-generated projection |
| 2 | `A B : ℤ` | integer coefficients | ring elements | yes | same as above — but irrelevant to whether *this projection lemma* is mathlib-worthy |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it fixes `R = ℤ`), but this is
immaterial: the declaration is not a candidate-for-`as-is`-or-generalise theorem. It is a
structure-field projection that, in any generality, is auto-generated by `@[simps]` on the
defining `def`. Generalising the *base ring* belongs to the `shortCurveZ` *definition*, not to
this projection lemma. Number of weakening opportunities on the lemma qua lemma: 0.
Cost of restatement: n/a (the lemma should not exist as a standalone mathlib decl at all).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | bundled-hypotheses → typeclasses/instances? | no | — | no hypotheses present |
|  2 | sequences/metric → filters/topological? | no | — | no analytic content |
|  3 | construction → universal-property class? | no | — | it's a coordinate read-off |
|  4 | set-with-predicate → bundled substructure? | no | — | n/a |
|  5 | vector-space/field-specific → weaken typeclass? | partial | generalize `shortCurveZ` to `ofShort {R} [CommRing R]` and let `@[simps]` emit the projections | the projection lemma itself is auto-derived, never hand-written |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → general algebraic structure? | yes (for the *def*) | `ofShort` over a general ring | but, again, the *lemma* is then `@[simps]` output, not a contribution |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it targets the `def`, not this lemma.** The mathlib-idiomatic
move is: if `shortCurveZ` (or a general `ofShort`) were defined, put `@[simps]` on it and *delete
all five `shortCurveZ_a₁..a₆` lemmas* — `@[simps]` generates `shortCurveZ_a₂ : (shortCurveZ A
B).a₂ = 0` automatically with the same `@[simp]` attribute. This is exactly how mathlib's own
`WeierstrassCurve.map` works (`@[simps]` at `Weierstrass.lean:230`, generating `map_a₁..map_a₆`).
Real mathematical improvement: removes five hand-written boilerplate projection lemmas in favour
of one attribute. But this is a *project-hygiene* refactor, not a mathlib contribution — the
generated lemma is no more mathlib-worthy than the hand-written one.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths
introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       "shortCurveZ a₂ = 0", "short Weierstrass a2 zero"  — no hits (concept absent as named decl; index unavailable locally, reasoned from source)
[B] Loogle            `(WeierstrassCurve.a₂ _ = 0)`, `?W.a₂ = 0`         — no *specific* hit; the *general* projection facts exist as `@[simps]` output and normal-form lemmas (below)
[C] LeanSearch        "a₂ coefficient of short Weierstrass curve is zero" — no hit for *this* curve
[D] Grep mathlib src  `\.a₂ = ` over `Mathlib/AlgebraicGeometry/EllipticCurve/` — relevant hits:
      - `NormalForms.lean:199`  `theorem a₂_of_isShortNF : W.a₂ = 0 := IsShortNF.a₂`  ← mathlib's *general* "short normal form ⇒ a₂ = 0"
      - `NormalForms.lean:562`  `theorem a₂_of_isCharTwoJEqZeroNF : W.a₂ = 0`
      - `VariableChange.lean:179` `variableChange_a₂ ... := rfl`  (projection-via-`rfl`, same shape)
      - `Weierstrass.lean:230`  `@[simps] def map` ⇒ auto-generated `map_a₂ : (W.map f).a₂ = f W.a₂`
[E] Name pattern      grep `shortCurve`, `ofShort`, `y\^2 = x\^3` in mathlib EllipticCurve dir — **no `shortCurveZ`/`ofShort` constructor in mathlib at all**

Searched for both:
  - the user's current form `(shortCurveZ A B).a₂ = 0` — not in mathlib (the def doesn't exist there)
  - the literature-standard form (short normal form has `a₂ = 0`) — **mathlib HAS this** as the
    typeclass-predicated `WeierstrassCurve.a₂_of_isShortNF` (`NormalForms.lean:199`), via the
    `IsShortNF W` predicate.

Concluded: **not in mathlib as-is (no `shortCurveZ` exists), but the underlying fact is fully
covered**: (a) mathlib's general "short normal form ⇒ `a₂ = 0`" is `a₂_of_isShortNF`; and (b) for
a concrete structure literal, mathlib's standard tool is `@[simps]`, which auto-emits exactly this
projection (cf. `map`'s `@[simps]`). So mathlib provides both the *general theorem* and the
*mechanism* — what's missing is only the project-local `def`, which is not a mathlib object.

---

### Call sites — `LutzNagell.LutzNagellTheorem.shortCurveZ_a₂` (Phase 6.0)

Internal use count: **0** as an explicit term (it is a `@[simp]` lemma — consumed by `simp`, not
named). Grep `shortCurveZ_a₂` across `projects/**.lean` excluding the declaring line: **0 hits**.

External-to-file callers (as a `simp` set member, by sibling name `shortCurveZ_a₁`/`_a₃` appearing
in explicit `simp only` calls — `shortCurveZ_a₂` is reachable by the same `simp` but not named):

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `GeneralMain.lean:167` | `simp only [curveQ_a₁, curveQ_a₃, shortCurveZ_a₁, shortCurveZ_a₃, …]` (siblings named; `_a₂` rides the global `@[simp]`) |

`shortCurveZ_a₂` itself appears in **zero** explicit `simp only` lists and **zero** term positions
— it is used, if at all, only as a member of the default `simp` set when `shortCurveZ` is unfolded
inside `shortCurveQ_*`, `shortCurveZ_delta`, and `shortCurveQ_equation_iff` (all in the declaring
file).

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - The pattern `(shortCurveZ _ _).a₂` is never written elsewhere; downstream code unfolds via
    `simp [shortCurveZ]` directly (e.g. `shortCurveZ_delta` at line 60 uses `simp [..., shortCurveZ]`,
    bypassing the named projection lemma entirely). This is the K=0 + inline-re-derivation signal:
    the projection lemmas are partly redundant with `simp [shortCurveZ]`.

### Composition check (Phase 6)

Can `(shortCurveZ A B).a₂ = 0` be derived from mathlib (+ the project `def`) in ≤3 calls?

Attempt 1: `rfl`.
  - Mathlib decls used: none — it's a structure-projection definitional equality.
  - Result: **succeeds** (it is literally the lemma's own proof).
Attempt 2 (mechanism-level): put `@[simps]` on `shortCurveZ` and delete the lemma.
  - `@[simps]` generates `shortCurveZ_a₂ : (shortCurveZ A B).a₂ = 0` with `@[simp]`, identically.
  - Result: **succeeds** — zero hand-written lemmas needed.

Conclusion: **COMPOSABLE** (degenerate — `rfl`, or equivalently the `@[simps]` attribute). No new
lemma is warranted: either `simp [shortCurveZ]` / `rfl` inline, or `@[simps]` on the def.

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveZ_a₂`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the "result" is the *definition* of short Weierstrass form; no
  source states "a₂ of the short model is 0" as a lemma. Project-specific scaffolding.
- Generality analysis (Phase 4): not a generalisable theorem; the only modern-idiom move
  (`@[simps]`) targets the *def* and would *delete* this lemma.
- Mathlib search (Phase 5): no `shortCurveZ`/`ofShort` exists in mathlib; the general fact is
  `WeierstrassCurve.a₂_of_isShortNF` (`NormalForms.lean:199`), and the mechanism is `@[simps]`
  (cf. `WeierstrassCurve.map`, `Weierstrass.lean:230`).
- Composition check (Phase 6): COMPOSABLE — `rfl`, or `@[simps]` auto-generation.

**Rationale:**

`shortCurveZ_a₂` is a one-line `rfl` structure-field projection: `shortCurveZ A B` is the literal
`{ a₁ := 0, a₂ := 0, … }`, so reading `.a₂` back gives `0` definitionally. It carries no
mathematical content beyond the coordinate convention that defines the short Weierstrass form, and
the literature uniformly treats "`a₂ = 0`" as *part of the definition* of that form, never as a
result. It is tied to a project-local `def` (`shortCurveZ` over `ℤ`) that does not exist in
mathlib and is pure Lutz–Nagell scaffolding.

Mathlib already supplies everything relevant: the *general* statement "short normal form ⇒ `a₂ =
0`" is `WeierstrassCurve.a₂_of_isShortNF` (predicated on the `IsShortNF` typeclass), and the
*idiomatic mechanism* for a concrete structure literal is `@[simps]`, which mathlib itself uses on
`WeierstrassCurve.map` (`Weierstrass.lean:230`) to auto-emit exactly these `_a₁..a₆` projections
with `@[simp]`. So no new mathlib lemma is needed: the fact is `rfl`, and the canonical way to
expose it is the `@[simps]` attribute on the definition — which would *delete* the five
hand-written `shortCurveZ_a₁..a₆` lemmas. This is a project-hygiene refactor, not a contribution.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the user's form is a 0-call (`rfl`) / attribute-level
composition. The "building block" is the `@[simps]` simp-lemma generator (and, at the term level,
plain `rfl` / `simp [shortCurveZ]`). Inlining is mechanical.

Mathlib building blocks:
  - `@[simps]` attribute — auto-generates structure-projection `@[simp]` lemmas (used by
    `WeierstrassCurve.map`, `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`)
  - structure-projection `rfl` (every consumer can also `simp [shortCurveZ]`, as
    `shortCurveZ_delta` already does at `ShortWeierstrass.lean:60`)
  - (general fact, if ever wanted abstractly) `WeierstrassCurve.a₂_of_isShortNF`
    (`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean:199`)

Composition sketch (≤3 lines):
```lean
-- Option A (preferred, project-local): annotate the def and delete the 5 projection lemmas
@[simps] def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }
-- now `shortCurveZ_a₂ : (shortCurveZ A B).a₂ = 0` is generated automatically, @[simp]

-- Option B (at any call site that needs it explicitly):
example (A B : ℤ) : (shortCurveZ A B).a₂ = 0 := rfl
```

Call sites in our project (from Phase 6.0): **K = 0** explicit uses; reachable only as a member of
the global `@[simp]` set inside the declaring file's own `shortCurveQ_*` / `*_delta` /
`*_equation_iff` lemmas.

Refactor plan: this is **project hygiene, not mathlib work** (`shortCurveZ` is not a mathlib
object). On the NagellLutz side, replace the five hand-written `shortCurveZ_a₁..a₆` lemmas
(`ShortWeierstrass.lean:32–36`) with `@[simps]` on `shortCurveZ` (and analogously `@[simps]` /
`map_*` reuse for the `shortCurveQ_a₁..a₆` block, since `shortCurveQ = shortCurveZ.map …` and
mathlib already provides `map_a₂` etc.). No call-site edits are required because the generated
lemmas keep the same names and `@[simp]` status. Do **not** submit `shortCurveZ_a₂` to mathlib.

Next action: keep `shortCurveZ_a₂` out of mathlib. Optionally, file a NagellLutz cleanup ticket to
replace the manual projection lemmas with `@[simps]` on `shortCurveZ` (and lean on mathlib's
`map_a₁..a₆` for the `shortCurveQ` variants).

---

## Next step

Keep `shortCurveZ_a₂` out of mathlib — it is a definitional `rfl` projection of a project-local
short-Weierstrass `def`, auto-derivable via `@[simps]` (the mechanism mathlib already uses on
`WeierstrassCurve.map`). Project-side, replace the hand-written `shortCurveZ_a₁..a₆` lemmas with
`@[simps]` on `shortCurveZ`.
