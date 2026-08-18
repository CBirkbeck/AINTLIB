# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveQ`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl reasoned from source.
- decl `LutzNagell.LutzNagellTheorem.shortCurveQ`:  ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:29`
- qualified name:           `LutzNagell.LutzNagellTheorem.shortCurveQ`
  (file opens `namespace LutzNagell` then `namespace LutzNagellTheorem`; the
  parsed guess in the prompt is **correct**)
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + A·x + B`
  over `ℤ` and its base change to `ℚ`, plus rewriting lemmas (equation, discriminant).

---

### Statement (Phase 1)

`shortCurveQ A B` is **a definition**: given integers `A B : ℤ`, it produces the
short Weierstrass curve `y² = x³ + A·x + B` viewed over `ℚ`. Concretely it takes
the integral model `shortCurveZ A B : WeierstrassCurve ℤ` (with `a₁=a₂=a₃=0,
a₄=A, a₆=B`) and **base-changes it to `ℚ`** along the canonical ring map
`algebraMap ℤ ℚ`.

The exact body:

```lean
def shortCurveQ (A B : ℤ) : WeierstrassCurve ℚ :=
  (shortCurveZ A B).map (algebraMap ℤ ℚ)
```

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the two coefficients of the short model.

Hypotheses (Lean side): none.

Conclusion (math): the rational elliptic/Weierstrass curve obtained by extending
the scalars of the integral curve `y² = x³ + Ax + B` from `ℤ` to `ℚ`.

Conclusion (Lean): `WeierstrassCurve ℚ` (n/a — it is a definition, not a proof).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `def` that is a one-line specialisation of the existing mathlib
operation `WeierstrassCurve.map`/`baseChange`; it introduces no new mathematical
structure and is not a named theorem. (Literature width run EXHAUSTIVE anyway.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`(shortCurveZ A B).map (algebraMap ℤ ℚ)`).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no | Downstream proofs (`shortCurveQ_a₄`, `shortCurveQ_equation_iff`) *unfold* `shortCurveQ` immediately via `simp [shortCurveQ, shortCurveZ]`; nothing relies on a sealed barrier. It is sealed (not `@[reducible]`) but is unfolded at every use, so the seal buys nothing. |
| Avoid typeclass diamonds         | no | No instance resolution hangs off this name; `WeierstrassCurve ℚ` instances come from mathlib regardless. |
| Mark semantic intent / API name  | no (weak) | The name is convenient locally, but the sibling `curveQ` (`GeneralCurve.lean:24`) already plays this exact role generically as an `abbrev`; the project does not need a *bespoke* sealed `shortCurveQ` to mark intent — `(shortCurveZ A B).baseChange ℚ` is equally legible. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** → biases the verdict toward
NO-composable-from-mathlib / NO-mathlib-has-it.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "base change of an elliptic curve to a field Weierstrass equation definition"                  | yes  | base-extend a Weierstrass model `y²+a₁xy+…` along a field/ring inclusion | Wikipedia *Elliptic curve*; Stanford crypto notes; LMFDB `ec.weierstrass_coeffs`; SageMath `base_extend` |
|  2 | WebSearch (general form)         | "short Weierstrass curve y^2 = x^3 + Ax + B over Q from integers Nagell-Lutz"                  | yes  | `y²=x³+Ax+B`, `A,B∈ℤ`, viewed over `ℚ`; Δ = −16(4A³+27B²) | Wikipedia *Nagell–Lutz*; Alpoge "Nagell-Lutz quickly"; MIT 18.782 lec 24 — this *is* the standard Nagell–Lutz setup |
|  3 | WebSearch (named-after / aliases)| "mathlib WeierstrassCurve baseChange map algebraMap elliptic curve over Q"                     | yes  | mathlib `WeierstrassCurve.baseChange`/`map` | confirms the operation is "base change"; mathlib `Reduction.lean` base-changes a curve to a field exactly this way |
|  4 | ChatGPT MCP                      | (server down per task note — substituted by WebSearch #1–#3 at three generality levels, which already pin the standard form unambiguously) | n/a | — | fallback used as the skill permits when the MCP is unavailable |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                            | n/a  | (directory absent) | `projects/NagellLutz/.mathlib-quality/` has only `overview/`; no `references/` dir |
|  6 | nLab                             | "base change elliptic curve / scalar extension"                                                | n/a  | — | base change of schemes is standard; nLab adds nothing beyond "pullback along Spec k → Spec ℤ". Not load-bearing for a coefficient-level Weierstrass def. |
|  7 | nCatLab                          | —                                                                                              | n/a  | — | not a categorical subtlety; it is `apply ringHom to each coefficient`. |
|  8 | Stacks Project                   | "base change of a scheme"                                                                      | n/a  | — | Stacks treats base change of schemes (Tag 01JX etc.); the *Weierstrass-coefficient* form here is the affine shadow of that, already in mathlib. |
|  9 | MathOverflow / MSE               | "elliptic curve base change to bigger field generality"                                        | n/a  | — | nothing controversial: base change of a Weierstrass model is textbook (Silverman III.1). |
| 10 | recent arXiv (last 5 years)      | "Nagell-Lutz formalization elliptic curve base change"                                          | yes  | confirms setup; the formalisation work uses mathlib's `WeierstrassCurve` | e.g. arXiv:2302.10640 (group law formalisation) builds on the same `WeierstrassCurve.map`/`baseChange` API |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels
(specific operation, the Nagell–Lutz short-model context, mathlib's own naming);
ChatGPT MCP unavailable → fallback documented; local refs recorded `n/a` (absent);
nLab / nCatLab / Stacks / MathOverflow / arXiv each checked with a one-line reason.

### Literature summary (Phase 3)

Concept identified as: **base change (scalar extension / base extension) of a
Weierstrass model of an elliptic curve** — here the short model `y²=x³+Ax+B`
from `ℤ` to `ℚ`.
Sources agree on the standard form: **yes** — "base-extend the Weierstrass model
along the ring map"; coefficient-wise application of the map. The "short" model
(`a₁=a₂=a₃=0`) is the standard char ≠ 2,3 reduced form, and `ℤ → ℚ` is its
canonical fraction-field embedding.
Most general standard form: base change of a Weierstrass curve over a commutative
ring `R` along **any** ring homomorphism `R →+* A` (mathlib's `WeierstrassCurve.map`),
or along an algebra structure (`baseChange`). `ℤ`, `ℚ`, and "short" are all
specialisations.
Generality dimensions where the literature varies:
  - base ring: from `ℤ` (here) up to an arbitrary `CommRing` (most general — mathlib's).
  - target: from `ℚ` (here) up to an arbitrary algebra / ring map (most general — mathlib's).
  - model shape: from "short" (`a₄=A,a₆=B`, rest 0) up to a full Weierstrass tuple.
Disagreement with the literature: **none**. `shortCurveQ` is a faithful, maximally
*narrow* instance of the standard operation.

---

### Generality analysis — `shortCurveQ`

Literature-standard form (Phase 3): base change of a Weierstrass curve along a ring
map `R →+* A` — i.e. mathlib's `WeierstrassCurve.map (f : R →+* A)` and the algebra
wrapper `WeierstrassCurve.baseChange A`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring fixed to `ℤ` | `shortCurveZ A B : WeierstrassCurve ℤ` | any `CommRing R` | yes | mathlib's `map`/`baseChange` already work over any `CommRing`; fixing `ℤ` is pure specialisation |
| 2 | target fixed to `ℚ`   | `.map (algebraMap ℤ ℚ)` | any `f : R →+* A` / algebra `A` | yes | the operation is identical for any ring map; `ℚ` is the fraction field, a special case |
| 3 | model shape "short"   | `a₁=a₂=a₃=0, a₄=A, a₆=B` | arbitrary `WeierstrassCurve` | yes | the sibling `curveQ W` (`GeneralCurve.lean:24`) is exactly the un-specialised version for arbitrary `W : WeierstrassCurve ℤ` |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (triple specialisation:
ring `ℤ`, target `ℚ`, short model). But the maximally general form is **already in
mathlib** as `WeierstrassCurve.map` / `WeierstrassCurve.baseChange` — so the right
move is not "generalise this def and ship it" but "use the existing general def".
Number of weakening opportunities: 3 (all subsumed by `map`/`baseChange`).
Cost of restatement: **CHEAP** (mechanical — replace by a `baseChange` call), but
the restatement target lives in mathlib, not in a new project def.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | bundled "let X be a foo" → typeclass? | no | — | already a plain `def` over typeclassed rings |
|  2 | sequences/metric → filters/topology? | no | — | no analytic content |
|  3 | construct object → universal-property class? | no | — | base change of a coefficient tuple is genuinely a construction; mathlib `map` is the right shape |
|  4 | set+closure-pred → bundled substructure? | no | — | n/a |
|  5 | field/metric-specific → weaken typeclass (module/ring)? | **yes** | use `WeierstrassCurve.map (f : R →+* A)` over a general `CommRing R`/target | the entire `map_a₁ … map_Δ`, `map_map`, `map_baseChange`, `map_injective` simp-API instantly applies |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index ℤ/ℚ → arbitrary structure? | **yes** | replace `(algebraMap ℤ ℚ)` by an arbitrary ring map / algebra | unifies with `baseChange` notation `W⁄A` and `IsScalarTower` lemmas |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is *literally mathlib's existing API*, not
a new formulation to add. The contemporary mathlib idiom for "the short ℤ-curve
viewed over ℚ" is `(shortCurveZ A B).baseChange ℚ` (or `(shortCurveZ A B)⁄ℚ`),
which is **definitionally equal** to the current body (`baseChange` unfolds to
`map (algebraMap ℤ ℚ)`). Real mathematical improvement: reusing `map`/`baseChange`
brings the whole simp-normal-form API (`map_a₄`, `map_Δ`, `map_injective`, …) for
free instead of re-proving `shortCurveQ_a₁ … shortCurveQ_a₆` by hand.

---

### Diamond / defeq risk — `shortCurveQ` (Phase 4.5)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | a `def` returning a `WeierstrassCurve ℚ` value; no instance is declared, so no search path is affected |
| 2 | Reducibility leak | none | not `@[reducible]`; sealed. (Indeed the project unfolds it manually everywhere — see 2b.) |
| 3 | Non-canonical unfolding | low | `simp [shortCurveQ]` unfolds to `map …`; harmless, and the project relies on exactly this |
| 4 | Instance priority collision | n/a | not an `instance` |
| 5 | Universe-polymorphism issues | none | fully monomorphic (`ℤ`, `ℚ`) |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. (Risk is not what kills this decl — redundancy is.)

---

### Mathlib search-status: `shortCurveQ`

[A] Lean-Finder       (mathlib-index MCP tools unavailable in this env)   n/a — tool not loadable; substituted with direct mathlib-source grep [D] + docs WebSearch
[B] Loogle            `WeierstrassCurve _ → (_ →+* _) → WeierstrassCurve _`  n/a — tool not loadable; the def `map` found directly in source instead
[C] LeanSearch        "base change Weierstrass curve over a ring map"        n/a — tool not loadable; covered by WebSearch #3 (mathlib4 docs) confirming `baseChange`/`map`
[D] Grep mathlib src  `def map`, `def baseChange`, `algebraMap` in `EllipticCurve/`  **HIT**: `WeierstrassCurve.map` at `Weierstrass.lean:231`; `WeierstrassCurve.baseChange` at `Weierstrass.lean:236`
[E] Name pattern      grep `baseChange` / `.map (algebraMap` across mathlib  **HIT**: `Reduction.lean:69` base-changes a `WeierstrassCurve` over a base ring to a field exactly this way

Searched for both:
  - the user's current form (`.map (algebraMap ℤ ℚ)`) — **is the body of `baseChange`**.
  - the literature-standard general form (`map` over any ring hom) — present as `WeierstrassCurve.map`.

Concluded: **found the building blocks** — `WeierstrassCurve.map`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:231`) and
`WeierstrassCurve.baseChange` (`…/Weierstrass.lean:236`). `shortCurveQ A B` is the
single call `(shortCurveZ A B).baseChange ℚ`, which is **defeq** to the current body
(`baseChange W A := W.map (algebraMap R A)`). Mathlib does **not** ship a pre-named
"this specific short curve over ℚ" — nor should it — so this is composition, not a
verbatim existing decl.

---

### Call sites — `shortCurveQ`

Internal use count: **4** (outside `ShortWeierstrass.lean`, excluding its own
`shortCurveQ_*` rewriting lemmas).
External-to-file callers: **2 distinct files** (`Main.lean`, `GeneralMain.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| LutzNagell/LutzNagellTheorem/Main.lean:36 | `{x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)` |
| LutzNagell/LutzNagellTheorem/Main.lean:49 | `{x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)` |
| LutzNagell/LutzNagellTheorem/Main.lean:67 | `{x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)` |
| LutzNagell/LutzNagellTheorem/GeneralMain.lean:154 | `{x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)` |

Inline-derivation grep (same statement re-derived elsewhere without `shortCurveQ`?):
  - The **general** version `curveQ W := W.map (algebraMap ℤ ℚ)` in
    `GeneralCurve.lean:24` is the same composition stated generically (an `abbrev`).
    `shortCurveQ` is effectively `curveQ (shortCurveZ A B)`. So the project already
    re-expresses this operation in two places, neither using a mathlib name.

Call-site signal: all 4 uses are `(shortCurveQ A B).toAffine.Nonsingular x y` — the
def is used purely as a notational shorthand for "the short curve over ℚ", never for
any property that `baseChange` wouldn't equally provide. K = 4 means it is *used*,
but the usage is replaceable 1-for-1 by `baseChange`.

---

### Composition check (Phase 6)

Can `shortCurveQ` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(shortCurveZ A B).baseChange ℚ`
  - Mathlib decls used: `WeierstrassCurve.baseChange` (which is `W.map (algebraMap R A)`).
  - Result: **succeeds** — `baseChange ℚ` unfolds to `map (algebraMap ℤ ℚ)`, the
    exact current body. This is `rfl`-equal to `shortCurveQ A B`.
  - Notes: 1 call. The coefficient lemmas `shortCurveQ_a₁ … shortCurveQ_a₆` are
    likewise the existing `map_a₁ … map_a₆` (alias `baseChange`) simp-lemmas
    combined with `shortCurveZ_a*`; no new lemma needed.

Conclusion: **COMPOSABLE** (a single `baseChange`/`map` call; defeq to the body).

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveQ`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the operation is "base change of a Weierstrass model
  from `ℤ` to `ℚ`" — textbook (Silverman III.1, SageMath `base_extend`, LMFDB).
- Generality analysis (Phase 4): STRICTLY NARROWER (triple specialisation), and the
  general form is already mathlib's `map`/`baseChange`.
- Mathlib search (Phase 5): building blocks `WeierstrassCurve.map`
  (`Weierstrass.lean:231`) and `WeierstrassCurve.baseChange` (`Weierstrass.lean:236`);
  the def body *is* `baseChange ℚ`.
- Composition check (Phase 6): COMPOSABLE — `(shortCurveZ A B).baseChange ℚ`, defeq.

**Rationale:**

`shortCurveQ A B` is a one-line, exemption-free `def` whose body
`(shortCurveZ A B).map (algebraMap ℤ ℚ)` is *literally* the definition of
`WeierstrassCurve.baseChange (shortCurveZ A B) ℚ` (mathlib defines
`baseChange A := map (algebraMap R A)`). Mathlib already provides the maximally
general operation (`map` over any ring hom, `baseChange` over any algebra) together
with its full simp API (`map_a₁ … map_Δ`, `map_map`, `map_baseChange`,
`map_injective`); mathlib's own `Reduction.lean` base-changes a curve over a base ring
to a field in exactly this idiom. So mathlib has the building block, not a pre-named
"short curve over ℚ" — and it should not have the latter (it is the kind of
project-local shorthand that belongs at the call site, not in the library).

It is **not** `NO-mathlib-has-it`, because no single existing mathlib decl *is*
`shortCurveQ` verbatim — it is a (defeq) composition. It is **not** any YES bucket:
the Phase-2b one-liner has no defeq/diamond/API exemption (the project unfolds it on
every use), Phase 4b is STRICTLY NARROWER, and the "more general / modern" target is
mathlib's existing `baseChange`, so there is nothing new to upstream.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; `shortCurveQ` is a 1-call composition that is
furthermore definitionally equal to that call. The same is true of the sibling
`curveQ` (`GeneralCurve.lean:24`), so the project is carrying two un-named-from-mathlib
aliases of `baseChange`.

Mathlib building blocks:
  - `WeierstrassCurve.baseChange` — `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:236`
  - `WeierstrassCurve.map`        — `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:231`
  - coefficient simp-lemmas `map_a₁ … map_a₆`, `map_Δ` — same file, lines 230–275.

Composition sketch (≤3 lines):
```lean
-- shortCurveQ A B  is defeq to:
example (A B : ℤ) : shortCurveQ A B = (shortCurveZ A B).baseChange ℚ := rfl
-- so at a call site:  (shortCurveZ A B).baseChange ℚ
```

Call sites in our project (from Phase 6.0): **K = 4** (Main.lean:36,49,67;
GeneralMain.lean:154), all of the form `(shortCurveQ A B).toAffine.Nonsingular x y`.

Refactor plan (note this is a *cleaner*-lane decision, not a producer change —
flagged here, do not edit `.lean` in this read-only assessment):
  1. Replace the def `shortCurveQ A B` with `(shortCurveZ A B).baseChange ℚ` (or
     `abbrev shortCurveQ A B := (shortCurveZ A B).baseChange ℚ` if a local name is
     still wanted) — both are defeq to the current body, so no proof breaks.
  2. At each of the 4 call sites, either keep the local name or inline
     `(shortCurveZ A B).baseChange ℚ`.
  3. Drop `shortCurveQ_a₁ … shortCurveQ_a₆` in favour of mathlib's `map_a₁ … map_a₆`
     (with `shortCurveZ_a*`); these are already proved upstream.
  4. Strongly consider unifying with the existing general `curveQ` abbrev so the
     project has *one* base-change alias, not two — ideally just mathlib's
     `baseChange`.

**Next action:** treat as a cleanup/dedup item — replace `shortCurveQ` (and align
`curveQ`) with `WeierstrassCurve.baseChange`; inline at the 4 call sites; delete the
hand-proved coefficient lemmas in favour of mathlib's `map_*`. No mathlib PR.
