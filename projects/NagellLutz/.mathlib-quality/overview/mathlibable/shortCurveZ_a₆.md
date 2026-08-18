# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveZ_a₆`

> Step-9 overview mathlibable assessment, single declaration. Project: NagellLutz
> (Nagell–Lutz theorem; short Weierstrass curves over ℤ/ℚ; division polynomials;
> elliptic divisibility sequences).

## Baseline (Phase 0)

- lake build:               (stale local build — assessed from source, per task brief; mathlib pinned `09b373db6e24`)
- decl `LutzNagell.LutzNagellTheorem.shortCurveZ_a₆`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:36`
- qualified name (VERIFIED from source): `LutzNagell.LutzNagellTheorem.shortCurveZ_a₆`
  (namespaces `LutzNagell` → `LutzNagellTheorem`, opened at lines 19–20, closed 64–65)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- body:                      `:= rfl`  (glue lemma)
- module docstring summary:  "Short Weierstrass model for Lutz–Nagell" — sets up
  `y² = x³ + A·x + B` over ℤ and its base change to ℚ, plus rewriting lemmas.

Exact source line:

```lean
@[simp] lemma shortCurveZ_a₆ (A B : ℤ) : (shortCurveZ A B).a₆ = B := rfl
```

where (lines 24–26)

```lean
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }
```

## Statement (Phase 1)

`shortCurveZ_a₆` is a **structure-projection glue lemma**. It states that the
`a₆` coefficient of the project-local short Weierstrass curve `shortCurveZ A B`
— defined as the anonymous constructor `{ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }`
of mathlib's `WeierstrassCurve ℤ` — equals `B`.

In board mathematics this is not a theorem at all: it is the defining equation of
the curve. "The constant term of `y² = x³ + Ax + B` is `B`" is true by how the
object was written down. The Lean content is purely definitional: projecting the
`a₆` field out of a literal record returns the value placed in that field, so the
proof is `rfl`.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the two free coefficients of the short Weierstrass model.

Hypotheses (Lean side): none.

Conclusion (math): the `a₆`-coefficient of the curve `shortCurveZ A B` is `B`.
Conclusion (Lean): `(shortCurveZ A B).a₆ = B`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `:= rfl` field-projection lemma about a project-local `def`; not a named
theorem, not a `## Main results` entry, introduces no new mathematical structure.

(Literature width is EXHAUSTIVE regardless — recorded below — but the concept is
"the `a₆` of a short Weierstrass equation", which is a definitional unfolding, not
a literature object.)

## One-line check (Phase 2b)

This is a `lemma` (not a `def`/`abbrev`/`structure`), so the one-liner-definition
gate is **n/a**. But the spirit applies: the body is a single `rfl`, the lemma is a
glue/unfolding lemma, and Mode-B verdict-inheritance rules treat `:= rfl` lemmas as
glue that inherit the parent `def`'s verdict rather than getting an independent life
in mathlib.

## Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "short Weierstrass equation" `y^2 = x^3 + Ax + B` coefficients `a₆`                            | yes  | `a₆ = B`, `a₄ = A`, `a₁=a₂=a₃=0` | Silverman *AEC* III.1; the short model is the *definition* — `a₆` is literally the constant `B`. Not a theorem in the literature. |
|  2 | WebSearch (general form)         | Weierstrass curve `aᵢ` coefficients general form `Y²+a₁XY+a₃Y=X³+a₂X²+a₄X+a₆`                   | yes  | the five `aᵢ` are *given data* of the curve | Tate/Silverman; the `aᵢ` are inputs, so "`a₆ = B`" is a tautology once the short model fixes them. |
|  3 | WebSearch (named-after / aliases)| "Nagell-Lutz" short Weierstrass coefficient lemma / "depressed cubic" constant term            | no   | —                   | No source states "the `a₆` of the short model is `B`" as a result; it is the construction. |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback) "Is `a₆ = B` for `y²=x³+Ax+B` ever stated as a lemma, and at what generality?" | n/a  | reasoned fallback: it is definitional, never a standalone lemma; generality question is vacuous | MCP unavailable; substituted reasoning from sources #1–#2. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                        | n/a  | directory absent    | No `references/` dir under the project — recorded n/a. |
|  6 | nLab                             | "Weierstrass curve" / "elliptic curve" coefficients                                            | n/a  | —                   | nLab covers elliptic curves abstractly; no per-coefficient projection statement (it would be a structure field, not a theorem). |
|  7 | nCatLab (categorical)            | —                                                                                             | n/a  | —                   | Not a categorical concept; a field projection of a record. |
|  8 | Stacks Project (alg geom)        | Weierstrass equation coefficients                                                             | n/a  | —                   | Stacks treats Weierstrass equations; the `aᵢ` are coefficients of the defining polynomial, i.e. data — no "`a₆ = B`" lemma. |
|  9 | MathOverflow / Math.SE           | short Weierstrass constant term `B` generality                                                | no   | —                   | No Q&A treats this as a fact; it is notation. |
| 10 | recent arXiv (last 5 yrs)        | elliptic divisibility sequence / division polynomial short model coefficients                 | no   | —                   | Coefficient `a₆=B` is assumed, never proved. |

### Literature summary (Phase 3)

Concept identified as: **the `a₆` coefficient of the short Weierstrass model
`y² = x³ + Ax + B`** — i.e. the constant term of the defining cubic.
Sources agree on the standard form: yes — universally, the short model *fixes*
`a₁=a₂=a₃=0`, `a₄=A`, `a₆=B`. This is a *definition*, not a theorem.
Most general standard form: the general Weierstrass curve carries five coefficients
`aᵢ` as given data (Silverman *AEC* III; Stacks). "The `a₆` is `B`" is the act of
writing the short model down — there is no more general theorem to state.
Generality dimensions where the literature varies: none relevant — the `aᵢ` are
inputs over an arbitrary base ring; the *only* mathematical content here is
"projecting a record field returns that field", which is definitional.
Disagreement with the literature: none — the lemma agrees trivially.

**Signal:** the literature returns no *theorem* for this, only the *definition*.
Per the Phase-3 guidance, "no standard-form theorem after a full protocol" is itself
a signal that the declaration is a definitional unfolding, not a mathlib-worthy
result. This steers Phase 7 toward a NO bucket.

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the five `aᵢ` are given data of a
Weierstrass curve over a base ring; the short model assigns them.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `A B : ℤ`              | integer coefficients | element of any base ring `R` | yes (cosmetically) | The *general* fact "projection of `{… a₆ := B}` is `B`" holds over any type and needs no `CommRing`. But generalising doesn't yield a *mathlib lemma* — it yields `rfl`, which mathlib already gives via `@[simps]`. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** *in content* (it is `rfl`; there is
nothing to weaken that produces a non-trivial general lemma). Generalising `ℤ → R`
just produces another `rfl` that `@[simps]` would auto-generate.
Number of weakening opportunities found: 0 (that yield a non-trivial mathlib lemma).
Proposed restatement: none — any restatement is still `rfl`.
Cost of restatement: n/a.

### 4c. Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
|  1 | bundled hyps → typeclasses? | no | — | no hypotheses to bundle |
|  2 | sequences/metric → filters/topology? | no | — | no analytic content |
|  3 | construction → universal property? | no | — | a record field, not a construction |
|  4 | set+closure → bundled substructure? | no | — | n/a |
|  5 | vector-space/field → module/(semi)ring? | no | — | n/a |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index (ℤ) → general additive structure? | partial | `(shortCurveZ A B).a₆ = B` over arbitrary `R` | none — still `rfl`; mathlib's `@[simps]` already emits projection-equals-field lemmas for any constructor. |

Modern idiom available: **no** (the only "modernisation" — letting `@[simps]`
auto-generate the projection lemmas — is a NO-composable observation, not a
restatement worth shipping).
One-line reason: there is no mathematical organisation to improve; the lemma is a
definitional projection that mathlib's own `@[simps]` attribute already produces
for free.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

## Mathlib search-status: `shortCurveZ_a₆` (Phase 5)

[A] Lean-Finder       "a₆ coefficient of short Weierstrass curve equals B"   no hit (no project-specific `shortCurveZ` in mathlib — expected; it's local)
[B] Loogle            `(WeierstrassCurve.a₆ _ = _)` / projection-of-curve pattern   the relevant mathlib decl is the **structure field** `WeierstrassCurve.a₆` itself (Weierstrass.lean:87) and the auto-`@[simps]` projection lemmas for `map` (`WeierstrassCurve.map_a₆`, Weierstrass.lean:231 `@[simps]`)
[C] LeanSearch        "coefficient a₆ of a Weierstrass curve" / "Weierstrass curve constant term"   matches the field accessor `WeierstrassCurve.a₆`; no standalone "= B" lemma (correctly — it would be about a *specific* curve)
[D] Grep mathlib src  `_a₆` standalone lemmas in `Mathlib/` → only `integralModel_a₆_eq` (Reduction.lean:116) and `variableChange_a₆` (VariableChange.lean:187), both about *named constructions*, not literal records; plus `@[simps] map` auto-emitting `map_a₆`
[E] Name pattern      `shortCurveZ_a₆` / `shortCurve*`   no hit in mathlib (project-local name)

Searched for both:
- the user's current form `(shortCurveZ A B).a₆ = B` — not in mathlib (it's about a
  project-local `def`, so it *cannot* be);
- the literature-standard / general form "projection of a Weierstrass-curve record
  field" — mathlib provides this as (i) the structure projection `WeierstrassCurve.a₆`
  itself, and (ii) `@[simps]`-generated projection lemmas (e.g. `WeierstrassCurve.map_a₆`).

Concluded: **found building blocks** — `WeierstrassCurve.a₆` (the field accessor,
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:87`) plus the language-level
`rfl`/`@[simps]` mechanism. The user's exact form is project-local (it mentions
`shortCurveZ`, a `def` that exists only in NagellLutz), so it is **not in mathlib and
cannot be** — but it is a zero-content composition of a mathlib field projection.

## Composition check (+ call-sites) (Phase 6)

### 6.0. Call sites — `shortCurveZ_a₆`

Internal use count: **0** (within NagellLutz, excluding the declaring file).
External-to-file callers: **0** distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Sibling-lemma cross-check (decisive context):

| Lemma            | External uses | Where |
|------------------|---------------|-------|
| `shortCurveZ_a₁` | **3** | `GeneralMain.lean:167`, `Main.lean:54`, `Main.lean:57` (in `simp only [...]` to rewrite the *vanishing* coefficient to 0) |
| `shortCurveZ_a₂` | 0 | — |
| `shortCurveZ_a₃` | **3** | `GeneralMain.lean:167`, `Main.lean:54`, `Main.lean:57` (same `simp only` sets) |
| `shortCurveZ_a₄` | 0 | — |
| `shortCurveZ_a₆` | **0** | — |

Inline-derivation grep (was `(shortCurveZ A B).a₆ = B` re-derived elsewhere?): **none.**
Downstream proofs never need to rewrite `a₆`/`a₄`/`a₂` because, where coefficients
matter (the discriminant / equation lemmas), they go through `shortCurveZ_delta`
(line 58) and `shortCurveQ_*`, or they only need the *zero* coefficients eliminated
(handled by `a₁`/`a₃`). The `a₆ = B` projection is `rfl`-transparent and simply never
referenced.

Call-sites signal (per the skill's table): **K = 0 internal uses, no inline
re-derivation.** For a `rfl` glue lemma this means it is unused — the only reason to
keep it locally is naming symmetry with the `a₁…a₆` family (uniform API surface), not
necessity.

### 6a. Composition attempt

Can `(shortCurveZ A B).a₆ = B` be derived from mathlib in ≤3 chained calls?

Attempt 1: `rfl`
  - Mathlib decls used: the `WeierstrassCurve.a₆` field projection (mathlib structure)
    applied to the anonymous constructor `shortCurveZ A B`.
  - Result: **succeeds.** Projecting `a₆` from `{ …, a₆ := B }` reduces to `B` by
    `rfl` (0 lemma calls — pure definitional unfolding).
Attempt 2: not needed.

Conclusion: **COMPOSABLE** — in fact zero-call `rfl`. Equivalently, deleting the
lemma and letting `@[simps]` on `shortCurveZ` (or just `simp`/`rfl` at any would-be
call site) discharge it costs nothing.

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveZ_a₆` (Phase 7)

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the "result" is the *definition* of the short
  Weierstrass model — no source states `a₆ = B` as a theorem; it is notation/data.
- Generality analysis (Phase 4): content is `rfl`; no non-trivial generalisation
  exists (any generalisation is still `rfl`, which `@[simps]` auto-emits). No modern
  idiom worth shipping.
- Mathlib search (Phase 5): building blocks present — the `WeierstrassCurve.a₆` field
  accessor (`Weierstrass.lean:87`) plus language-level `rfl`/`@[simps]`. The exact
  form is project-local (mentions `shortCurveZ`) and cannot live in mathlib.
- Composition check (Phase 6): COMPOSABLE — discharged by `rfl` (0 calls);
  **K = 0 call sites**, no inline re-derivation.

**Rationale.** `shortCurveZ_a₆` is a `:= rfl` projection lemma about a project-local
`def shortCurveZ`. It cannot go into mathlib as-is because it names a NagellLutz-only
object; and there is nothing general behind it to upstream — the only general fact is
"a structure projection of a constructor returns the field value", which is `rfl` and
which mathlib already automates with the `@[simps]` attribute (indeed mathlib's own
`@[simps] def map` auto-generates exactly this style of lemma, `WeierstrassCurve.map_a₆`).
So mathlib has the *building block* (the `a₆` accessor and the projection mechanism),
not — and not needing — this specific equation. It belongs in the project, discharged
by `rfl`/`simp`, and never reaches a mathlib PR.

WHY not (refactor-actionable):
- Mathlib has the building blocks: the field projection `WeierstrassCurve.a₆`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:87`) and the `@[simps]`
  attribute that auto-emits projection-equals-field lemmas (cf. the auto-generated
  `WeierstrassCurve.map_a₆` from `@[simps] def map`, Weierstrass.lean:231). The user's
  form is the *0-call* `rfl` specialisation of this at the literal record
  `shortCurveZ A B` — it is genuinely project-local, not a mathlib gap.
- Mathlib building blocks: `WeierstrassCurve.a₆` (field accessor); `@[simps]` /
  language-level `rfl`.
- Composition sketch (≤3 lines):
  ```lean
  example (A B : ℤ) : (shortCurveZ A B).a₆ = B := rfl
  ```
- Call sites in our project (from Phase 6.0): **K = 0.**
- Refactor plan: there are no call sites to update. The lemma is unused. Two equally
  valid local actions (both leave `main` green; neither is a mathlib PR):
  1. **Keep for API symmetry** — it rounds out the `shortCurveZ_a₁ … a₆` simp family
     and costs nothing (it is `rfl`). This is the conservative choice and is fine for
     a WIP project; the used siblings (`a₁`, `a₃`) justify the family's existence.
  2. **Drop the unused members** — if minimising surface is preferred, delete
     `shortCurveZ_a₆` (and likewise the also-unused `shortCurveZ_a₂`, `shortCurveZ_a₄`),
     since any future need is met by `simp [shortCurveZ]` or by tagging `shortCurveZ`
     with `@[simps]`. No consumer breaks (K = 0).

**Next action:** do **not** open a mathlib PR. This is a project-local `rfl` glue
lemma with no call sites. Either keep it for `a₁…a₆` family symmetry (zero cost) or,
if trimming, delete it alongside the equally-unused `shortCurveZ_a₂`/`a₄` and rely on
`simp [shortCurveZ]` / `@[simps]`. Not a mathlib contribution under any framing.
