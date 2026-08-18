# /mathlibable report — `LutzNagell.LutzNagellTheorem.curveQ_a₄`

### Baseline (Phase 0)
- lake build:               not run (env note: local build stale; reasoned from source + the mathlib tree, authoritative for this functoriality lemma)
- decl `LutzNagell.LutzNagellTheorem.curveQ_a₄`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:30`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "General Weierstrass model for the generalized Lutz–Nagell theorem" — sets up `W : WeierstrassCurve ℤ`, its base change `curveQ W` to ℚ, and basic rewriting lemmas (equation, coefficients).

Source:
```lean
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)

@[simp] lemma curveQ_a₄ : (curveQ W).a₄ = (W.a₄ : ℚ) := by simp [curveQ]
```

---

### Statement (Phase 1)

`curveQ_a₄` is a rewriting lemma stating: for an integral Weierstrass curve `W : WeierstrassCurve ℤ`,
the `a₄` coefficient of its base change to ℚ (`curveQ W := W.map (algebraMap ℤ ℚ)`) equals the
rational image of the integer coefficient `W.a₄`, i.e. `(curveQ W).a₄ = (W.a₄ : ℚ)`.

Mathematically this is the trivial functoriality statement "the map on a Weierstrass curve induced
by a ring homomorphism acts coordinate-wise on the `aᵢ`", specialised to `f = algebraMap ℤ ℚ` and to
the `a₄` coordinate.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — an integral Weierstrass curve.

Hypotheses (Lean side): none.

Conclusion (math): the `a₄` coefficient commutes with the base-change map ℤ → ℚ.
Conclusion (Lean): `(curveQ W).a₄ = (W.a₄ : ℚ)` — definitionally `((W.map (algebraMap ℤ ℚ)).a₄ = ((W.a₄ : ℤ) : ℚ))`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a coordinate-projection rewriting lemma — a 1-step specialisation of a mathlib `@[simps]`-generated lemma; not a structure, not a named theorem, not a project main result.

### One-line check (Phase 2b)

Kind is `lemma` (not a `def`/`abbrev`), so the one-line def check is n/a. Note: the proof body is a single tactic (`by simp [curveQ]`); this reinforces that the lemma is a trivial wrapper, not new content.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found                              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | base change Weierstrass curve coefficients a4 functoriality elliptic curve ring homomorphism  | yes  | `W.map f` acts coordinate-wise: `(W.map f).a₄ = f W.a₄` | Top hit is the mathlib `Weierstrass.html` doc page itself; confirms the coordinate-wise transformation as the standard construction |
|  2 | WebSearch (general form)         | (same query, general angle) "base change of Weierstrass models over a ring map"               | yes  | functorial coordinate-wise base change of `aᵢ`   | Silverman AEC III.1 / VIII: the `aᵢ` transform coordinate-wise under a ring hom; only the `(u,r,s,t)` change-of-variables is non-trivial |
|  3 | WebSearch (named-after / aliases)| "Weierstrass model base change" / Sage `weierstrass_morphism`, Magma elliptic curves handbook | yes  | same coordinate-wise rule                        | Sage/Magma realise the same: applying a ring map to `[a1,a2,a3,a4,a6]` is literally entrywise |
|  4 | ChatGPT MCP                      | (MCP down per env note — fallback used)                                                        | n/a  | —                                                | Substituted by WebSearch rows 1–3 + Loogle row 11, which already pin the standard form unambiguously |
|  5 | Local references                 | `.mathlib-quality/references/` for "map"/"base change"                                         | n/a  | (no references dir present for this triage)       | dir absent — recorded n/a |
|  6 | nLab                             | "Weierstrass curve" / "elliptic curve base change"                                             | n/a  | —                                                | nLab has no entry at the level of "coefficient of a base-changed Weierstrass equation"; concept too elementary |
|  7 | nCatLab (if categorical)         | —                                                                                             | n/a  | —                                                | not a categorical concept (it is a coordinate identity) |
|  8 | Stacks Project (if alg geom)     | "Weierstrass equation base change"                                                            | n/a  | —                                                | Stacks treats elliptic curves abstractly; no per-coefficient `aᵢ` base-change lemma at this granularity |
|  9 | MathOverflow / MSE               | "base change of Weierstrass coefficients"                                                     | n/a  | —                                                | nothing beyond the textbook coordinate-wise rule; not a research-level question |
| 10 | recent arXiv (last 5 years)      | "formal proof group law Weierstrass curves any characteristic" (arXiv 2302.10640)             | yes  | coordinate-wise `map` of `aᵢ`                    | The formalisation literature (and mathlib itself) treat `W.map f` entrywise — same as the decl |
| 11 | Loogle (mathlib index, fallback) | `(WeierstrassCurve.map _ _).a₄`                                                                | yes  | `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄` | Direct hit — mathlib already has this exact lemma (see Phase 5) |

### Literature summary (Phase 3)

Concept identified as: **functorial (coordinate-wise) base change of the Weierstrass coefficient `a₄` under a ring homomorphism**.
Sources agree on the standard form: yes — every source (Silverman AEC, Sage, Magma, the mathlib doc page, the formalisation arXiv paper) treats applying a ring map to a Weierstrass model as entrywise on `[a₁,a₂,a₃,a₄,a₆]`.
Most general standard form: for any ring homomorphism `f : R →+* A` and `W : WeierstrassCurve R`, `(W.map f).a₄ = f W.a₄`.
Generality dimensions where the literature varies:
  - base ring / target: the literature states it for an arbitrary ring map `R → A`; the decl fixes the single instance `ℤ → ℚ`.
Disagreement with the literature: none — the decl is the `R := ℤ, A := ℚ, f := algebraMap ℤ ℚ` specialisation of the standard statement.

---

### Generality analysis — `curveQ_a₄` (Phase 4)

Literature-standard form (from Phase 3): `∀ {R A} [CommRing R] [CommRing A] (f : R →+* A) (W), (W.map f).a₄ = f W.a₄`.

| # | Parameter / hypothesis | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|----------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | base ring `R`          | fixed to `ℤ`                     | arbitrary `CommRing R`           | yes                 | the identity is coordinate-wise; `ℤ` plays no role |
| 2 | target ring `A`        | fixed to `ℚ`                     | arbitrary `CommRing A`           | yes                 | `ℚ` plays no role |
| 3 | the map `f`            | fixed to `algebraMap ℤ ℚ`        | arbitrary `f : R →+* A`          | yes                 | any ring hom; the algebra structure is irrelevant |
| 4 | RHS coercion           | `(W.a₄ : ℚ)` (`Int.cast`)        | `f W.a₄`                         | n/a                 | `(W.a₄ : ℚ) = algebraMap ℤ ℚ W.a₄` by `algebraMap_int_eq` — same value, one cast-normalisation step |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (it is the `ℤ → ℚ` specialisation).
Number of weakening opportunities found: 3 (base ring, target ring, the map).
Proposed restatement: the fully general form is **already in mathlib** as `WeierstrassCurve.map_a₄` (Phase 5). So the right action is not to generalise-and-add, but to **delete and reuse the mathlib lemma**. (The generality gap is therefore moot — mathlib already occupies the general slot.)
Cost of restatement: n/a — no restatement to ship; the general form exists upstream.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
| 1  | bundled hypotheses → typeclasses/instances?                                                | no       | —                      | already maximally typeclass-driven via `f : R →+* A` |
| 2  | sequences/metric → filters/topology?                                                       | no       | —                      | purely algebraic coordinate identity |
| 3  | construct an object → universal-property class?                                            | no       | —                      | it is a projection equality, no object constructed |
| 4  | set-with-closure → bundled substructure?                                                   | no       | —                      | n/a |
| 5  | vector-space/field-specific → weaken typeclass?                                            | yes      | use a general `CommRing`/`RingHom` instead of `ℤ→ℚ` | this is exactly what mathlib's `map_a₄` already does |
| 6  | 1-categorical → higher-categorical?                                                        | no       | —                      | n/a |
| 7  | concrete index (ℤ/ℚ) → arbitrary structure?                                                | yes      | replace `ℤ,ℚ` by arbitrary `R,A` and `algebraMap` by a `RingHom` | again, precisely mathlib's `map_a₄` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes, but it **is the existing mathlib lemma** `WeierstrassCurve.map_a₄` — the "modernisation" (drop `ℤ→ℚ`, use a general `RingHom`) is already realised upstream. There is nothing new to ship; the move is to reuse, not to generalise-and-add. Hence this does not push toward YES-but-generalise-first.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `curveQ_a₄` (Phase 5)

[A] Lean-Finder       (index tool unavailable in env)                          n/a: deferred lean_* tools not loadable here; substituted by Loogle + direct source grep
[B] Loogle            `(WeierstrassCurve.map _ _).a₄`                            HIT → `WeierstrassCurve.map_a₄`
[C] LeanSearch        "a4 coefficient of base changed Weierstrass curve"        n/a: index tool unavailable; covered by [B]/[D]
[D] Grep mathlib src  `map_a₄` / `def map` in `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` | HIT
[E] Name pattern      `WeierstrassCurve.map_a₄` across mathlib + this repo       HIT (defined upstream; used by sibling HasseWeil project)

Searched for both:
  - the user's current form `(curveQ W).a₄ = (W.a₄ : ℚ)` — matches after unfolding `curveQ` + `algebraMap_int_eq`.
  - the literature-standard general form `(W.map f).a₄ = f W.a₄` — **direct hit**.

Key source evidence (mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`):
```lean
@[simps]                       -- ⇐ auto-generates map_a₁ … map_a₆ as @[simp] lemmas
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩
```
`@[simps]` on `map` generates `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄` (`@[simp]`). It is used as a simp lemma throughout the same file (lines 244–259: `simp only [b₄, map_a₁, map_a₃, map_a₄]`, etc.). Loogle returns it directly with statement `(W.map f).a₄ = f W.a₄`.

Concluded: **found in mathlib as `WeierstrassCurve.map_a₄`; more general form** (arbitrary `f : R →+* A`; the decl is the `f := algebraMap ℤ ℚ` specialisation).

---

### Call sites — `curveQ_a₄` (Phase 6.0)

Internal use count: **0**  (within NagellLutz, excluding the declaring file `GeneralCurve.lean`)
External-to-file callers: **0**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | `curveQ_a₄` is referenced only at its own declaration site, `GeneralCurve.lean:30` |

Notes:
- The sibling lemmas of the `curveQ_a*` family *are* consumed elsewhere — `grep` shows `GeneralMain.lean`, `GeneralDiscriminant.lean`, `GeneralPrimeOrder.lean` reference the family — but `curveQ_a₄` *specifically* has no call site outside its declaration (those files use other members and/or `simp` picks them up implicitly; `curveQ_a₄` is tagged `@[simp]` so it may fire inside `simp` calls, but there is no explicit named use anywhere).
- Inline-derivation grep: the same content is obtained inline downstream via `simp [curveQ]` / the `@[simps]`-generated `WeierstrassCurve.map_a₄`. Notably the sibling **HasseWeil** project in this monorepo already calls mathlib's `WeierstrassCurve.map_a₄` directly in `simp only` sets (e.g. `HasseWeil/LocalExpansion.lean:543`, `RouteBGeneral.lean:364`, `AdditionPullback/SilvermanIV14.lean:3088,3577`, `WeilPairing/FrobeniusDivisorGalois.lean:184`) — demonstrating the upstream lemma is the canonical, in-use tool for exactly this fact.

Call-sites signal: K = 0 internal uses, with the equivalent available upstream as `WeierstrassCurve.map_a₄` (a `@[simp]` lemma). Strong NO signal — this is a local re-statement of an existing upstream simp lemma.

### Composition check (Phase 6)

Can `curveQ_a₄` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(W.map (algebraMap ℤ ℚ)).a₄ = algebraMap ℤ ℚ W.a₄` is exactly `WeierstrassCurve.map_a₄`; then `algebraMap ℤ ℚ W.a₄ = (W.a₄ : ℚ)` by `algebraMap_int_eq` (`algebraMap ℤ R = Int.castRingHom R`).
  - Mathlib decls used: `WeierstrassCurve.map_a₄`, `algebraMap_int_eq` (+ `Int.coe_castRingHom` cast glue).
  - Result: succeeds — and indeed the project's own proof `by simp [curveQ]` is precisely this (unfold `curveQ`, apply the `@[simps]` `map_a₄`, normalise the int-cast).
  - Notes: ≤2 essential rewrites; well within the ≤3 budget. Strictly this is NO-mathlib-has-it (the general lemma exists) rather than a mere composition — it is `map_a₄` specialised, not a novel combination.

Conclusion: COMPOSABLE (degenerate — it is a direct specialisation of the existing `WeierstrassCurve.map_a₄`).

---

## Verdict: `LutzNagell.LutzNagellTheorem.curveQ_a₄`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard concept = coordinate-wise base change of Weierstrass `aᵢ`; Loogle row returns the exact mathlib lemma.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (the `ℤ→ℚ` specialisation) — but the general form is already upstream, so no generalise-and-add is warranted.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_a₄`; more general form (arbitrary `f : R →+* A`).
- Composition check (Phase 6): COMPOSABLE / direct specialisation.

**Rationale:**

This project forks mathlib's elliptic-curve files and re-introduces a `curveQ`-flavoured base-change track, but the coefficient lemma `curveQ_a₄` duplicates content mathlib already owns. Mathlib's `WeierstrassCurve.map` carries `@[simps]`, which auto-generates `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄` as a `@[simp]` lemma; Loogle returns it directly and it is used internally in `Weierstrass.lean` (lines 244–259). Since `curveQ W := W.map (algebraMap ℤ ℚ)`, the decl is the `f := algebraMap ℤ ℚ` specialisation of `map_a₄`; the only spelling gap is the RHS, where `(W.a₄ : ℚ)` (an `Int.cast`) equals `algebraMap ℤ ℚ W.a₄` by `algebraMap_int_eq`. That is one cast-normalisation rewrite — precisely what the existing proof `by simp [curveQ]` performs.

The lemma also has zero call sites of its own (the broader `curveQ_a*` family is used in three sibling files, but `curveQ_a₄` is referenced only at its declaration), and the sibling **HasseWeil** project in this same monorepo already uses mathlib's `WeierstrassCurve.map_a₄` directly for this exact fact. So nothing in NagellLutz depends on the `curveQ`-spelled variant that could not be served by the upstream simp lemma firing through `curveQ`'s unfolding. Mathlib should not gain a `ℤ→ℚ`-specialised duplicate of a lemma it already has in full generality.

**WHY not (refactor-actionable):**
Mathlib already has the fully general lemma `WeierstrassCurve.map_a₄`. The project decl is its `algebraMap ℤ ℚ` specialisation; the RHS differs only by `Int.cast` vs `algebraMap ℤ ℚ`, reconciled by `algebraMap_int_eq` in one simp step. No new lemma is owed to mathlib.

Existing mathlib decl:        `WeierstrassCurve.map_a₄`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` (auto-generated by `@[simps]` on `def map`, ~line 230; used at lines 244–259)
Our form follows in ≤1 line:
```lean
example (W : WeierstrassCurve ℤ) : (curveQ W).a₄ = (W.a₄ : ℚ) := by
  simp [curveQ]            -- unfolds curveQ, applies WeierstrassCurve.map_a₄, normalises Int.cast
-- equivalently, explicitly:
example (W : WeierstrassCurve ℤ) :
    (W.map (algebraMap ℤ ℚ)).a₄ = algebraMap ℤ ℚ W.a₄ := WeierstrassCurve.map_a₄ ..
```
Call sites in our project (from Phase 6.0): K = 0 (outside the declaring file).
Refactor plan: this is a **project-local cleanup, not a mathlib action**. Since `curveQ_a₄` has no external-to-file callers, it can simply be **deleted**; any place relying on it (only `simp` closures inside `GeneralCurve.lean`/siblings) is already covered because `simp [curveQ]` unfolds the `abbrev` and mathlib's `@[simp] WeierstrassCurve.map_a₄` then fires automatically, with `Int.cast` normalised by the default simp set. If a named handle is ever wanted, reference `WeierstrassCurve.map_a₄` directly (as the HasseWeil project already does). The same applies to the whole `curveQ_a₁/a₂/a₃/a₆` family — each duplicates the corresponding `@[simps]`-generated `WeierstrassCurve.map_aᵢ`.
Next action: drop `curveQ_a₄` (and ideally the sibling `curveQ_aᵢ` lemmas) from the project; rely on mathlib's `WeierstrassCurve.map_aᵢ` simp lemmas through `curveQ`'s unfolding. Nothing to upstream.

---

## Next step

Project-local: delete `curveQ_a₄` (no external callers); mathlib's `@[simp] WeierstrassCurve.map_a₄` already covers it via `simp [curveQ]`. No mathlib PR — `NO-mathlib-has-it`.
