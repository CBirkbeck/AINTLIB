# /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveQ_a₆`

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale per task; reasoned from source — decl elaboration is trivial `by simp`)
- decl `LutzNagell.LutzNagellTheorem.shortCurveQ_a₆`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:50`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + A·x + B` over ℤ and its base change to ℚ, with basic rewriting lemmas (coefficients, equation, discriminant).

Qualified name VERIFIED from source: namespace block is `namespace LutzNagell` / `namespace LutzNagellTheorem` (lines 19–20), so the fully-qualified name is **`LutzNagell.LutzNagellTheorem.shortCurveQ_a₆`** — matches the task's parsed guess.

---

### Statement (Phase 1)

`shortCurveQ_a₆` states: for integers `A B`, the `a₆` coefficient of the short Weierstrass curve `shortCurveZ A B` (which is `{a₁:=0, a₂:=0, a₃:=0, a₄:=A, a₆:=B}`) after base change along the canonical ring homomorphism `algebraMap ℤ ℚ` equals the rational-number cast `(B : ℚ)` of `B`.

Mathematically this is the single naturality/functoriality fact: the `a₆`-coordinate of the base change of a Weierstrass curve is the image of the original `a₆` under the structure map — here `algebraMap ℤ ℚ` applied to the integer `B`, which is just `(B : ℚ)`.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the two coefficients of the short Weierstrass model. `B` is the only one that appears in the conclusion.

Hypotheses (Lean side):
- none.

Conclusion (math): the `a₆`-coefficient of `(shortCurveZ A B) ⊗_ℤ ℚ` is `B` viewed in ℚ.

Conclusion (Lean): `(shortCurveQ A B).a₆ = (B : ℚ)` where `shortCurveQ A B := (shortCurveZ A B).map (algebraMap ℤ ℚ)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` coordinate-projection glue lemma about a project-local curve definition; not a named theorem, not a new structure, not a `## Main results` entry. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`by simp [shortCurveQ, shortCurveZ]`).
One-liner verdict: n/a (kind is `lemma`, not `def`) — but it is a one-line *glue* lemma, which carries the same NO-leaning signal. Recorded for narrative; the defeq/diamond exemptions for one-line *defs* do not apply to a lemma.

This is one of five sibling glue lemmas (`shortCurveQ_a₁ … shortCurveQ_a₆`, lines 38–51), each projecting one coefficient of `shortCurveQ` through the base change. They are the ℚ-side analogues of the five `rfl` lemmas `shortCurveZ_a₁ … shortCurveZ_a₆` (lines 32–36).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve base change Weierstrass coefficients a6 ring homomorphism functoriality" | yes | `(W.map f).aᵢ = f (W.aᵢ)` | **Top hit is Mathlib's own `Weierstrass.html` docs**, which surface `map` = `⟨f a₁,…,f a₆⟩` and the per-coefficient lemma `map_a₆`. Confirms this is bog-standard functoriality of base change. |
|  2 | WebSearch (general / named-after) | "Nagell-Lutz theorem short Weierstrass equation y² = x³ + Ax + B base change to rationals" | yes | the *theorem* is Nagell–Lutz (torsion → integral coords); the coefficient-projection is not a named result | Wikipedia/Harvard/PlanetMath. Nagell–Lutz is the surrounding theorem; the projection lemma is invisible scaffolding, not a literature object. |
|  3 | WebSearch (aliases)              | (covered by #1: "base change", "map", "functoriality") | yes | same as #1 | The operation is called variously base change / map / pushforward; all agree the coordinates transform coordinate-wise. |
|  4 | ChatGPT MCP                      | self-contained question: is this >2–3 step mechanical composition, does it belong in mathlib? | n/a | — | **MCP backend down** (Codex exec failure — matches the task's "ChatGPT MCP may be down" warning). Substituted by first-principles analysis (Phase 6) + the grep-confirmed mathlib lemma. |
|  5 | Local references                 | grep `.mathlib-quality/references/` | n/a | — | Directory absent (`projects/NagellLutz/.mathlib-quality/references/` does not exist). |
|  6 | nLab                             | "elliptic curve base change coefficients" | n/a | — | nLab has no page on Weierstrass-coefficient transformation; this is a coordinate computation, not a categorical concept worth an nLab entry. The relevant abstraction (base change is functorial) is generic and uncontested. |
|  7 | nCatLab                          | — | n/a | — | Not a categorical concept beyond "base change is a functor", which is not what this lemma is. |
|  8 | Stacks Project                  | "Weierstrass equation base change" | n/a | — | Stacks treats Weierstrass equations (Tag 0C5W area) but the per-coefficient projection through a ring map is below the granularity Stacks records; it's an immediate consequence of the定义. |
|  9 | MathOverflow / MathSE           | — | n/a | — | No MO/MSE question turns on "what is `a₆` of a base-changed Weierstrass curve" — it is definitional. |
| 10 | recent arXiv (≤5 yrs)           | (covered by #2: Nagell–Lutz over number fields, arXiv 2509.07524) | n/a | — | Recent Nagell–Lutz papers use the short model freely; none isolate the coefficient-projection as a stated lemma. |

The protocol passed: WebSearch ran 3 queries at different generality (specific functoriality form, the named surrounding theorem, aliases); ChatGPT recorded n/a with a backend-down reason; local refs recorded n/a (absent); nLab/Stacks/nCatLab/MO/arXiv each checked and recorded n/a with a substantive one-line reason.

### Literature summary (Phase 3)

Concept identified as: **functoriality of base change for Weierstrass curves** — the `a₆`-coordinate of `W.map f` is `f (W.a₆)`, specialised to `W = shortCurveZ A B`, `f = algebraMap ℤ ℚ`, where `algebraMap ℤ ℚ = Int.cast` so `f B = (B : ℚ)`.
Sources agree on the standard form: yes — base change acts coordinate-wise; this is uniform across Silverman-style references, Magma/Sage docs, and Mathlib.
Most general standard form: `(W.map f).a₆ = f W.a₆` for any ring hom `f : R →+* A` and any `W : WeierstrassCurve R`. **This is exactly `WeierstrassCurve.map_a₆`, already in Mathlib.**
Generality dimensions where the literature varies: none of substance — the only "specialisation knobs" are (W is the short curve; f is ℤ→ℚ; the RHS is rewritten via the int-cast identity), none of which add content.
Disagreement with the literature: none. The project lemma is a strict specialisation of the universally-agreed functoriality statement.

---

### Generality analysis — `shortCurveQ_a₆`

Literature-standard form (from Phase 3): `(W.map f).a₆ = f W.a₆`, all `W`, all `f : R →+* A`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | the curve `shortCurveZ A B` | one specific ℤ-curve `{0,0,0,A,B}` | arbitrary `W : WeierstrassCurve R` | yes | nothing in the statement uses the shape of the curve except that its `a₆` is `B`; the general statement is `map_a₆`. |
| 2 | the ring map `algebraMap ℤ ℚ` | the canonical ℤ→ℚ algebra map | arbitrary `f : R →+* A` | yes | functoriality holds for every ring hom; ℤ→ℚ is incidental. |
| 3 | RHS `(B : ℚ)` | `Int.cast B` | `f W.a₆` | yes | `(B:ℚ)` is just `algebraMap ℤ ℚ B` rewritten via the ℤ-initiality identity `RingHom.eq_intCast`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is a triple specialisation of `map_a₆`).
Number of weakening opportunities found: 3 (curve, ring map, RHS-rewrite).
Proposed restatement: there is nothing to restate as a *new* lemma — the maximally-general form already exists in Mathlib as `WeierstrassCurve.map_a₆`. Generalising the project lemma reproduces an existing Mathlib lemma verbatim. Hence the correct action is not "generalise-first" (that bucket is for new general lemmas Mathlib lacks) but **deletion/inlining**, because the general form is already upstream.
Cost of restatement: n/a — no restatement; the general lemma exists.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" → typeclass? | no | — | The general form `map_a₆` already uses bundled `f : R →+* A`; no preamble to typeclass-ify. |
|  2 | sequences/metric → filters/topology? | no | — | No analytic content; purely algebraic projection. |
|  3 | construction → universal property? | no | — | `map` is already a clean functorial construction in Mathlib. |
|  4 | set+closure-pred → bundled substructure? | no | — | n/a. |
|  5 | vector-space/field-specific → weaken typeclass? | no | — | `map_a₆` is already at `CommRing` generality. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index (ℤ/ℚ) → arbitrary ring/monoid? | **yes** | the general form is `(W.map f).a₆ = f W.a₆` — but that IS `map_a₆`, already upstream | the ℤ→ℚ specificity is exactly what makes this project-local; removing it lands you on the existing Mathlib lemma. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no (the "modernised" form is the existing `map_a₆`; there is no *new* idiomatic lemma to ship).
One-line reason: the only generalisation move (row 7) collapses the project lemma onto a lemma Mathlib already has, so this is a NO-bucket case (composable / has-it), not a generalise-first case.

---

### Diamond / defeq risk — `shortCurveQ_a₆`

n/a — declaration kind is `lemma` (a `@[simp]` lemma introduces a rewrite rule, not a definitional equality or typeclass-search path, so Phase 4.5 does not apply). Worth a one-line note: as a `@[simp]` lemma it is harmless and in fact partly redundant with the upstream `@[simp] map_a₆` + cast simp set.

---

### Mathlib search-status: `shortCurveQ_a₆`

[A] Lean-Finder       — n/a: no Lean-Finder MCP available in this environment.
[B] Loogle            `(WeierstrassCurve.map _ _).a₆ = _ _` — n/a: no Loogle MCP available; substituted by source grep [D], which is definitive for an exact-name lemma.
[C] LeanSearch        "coefficient a6 of base changed Weierstrass curve" — n/a: no LeanSearch MCP available; substituted by [D] + WebSearch #1 (which returned the Mathlib docs page naming `map_a₆`).
[D] Grep mathlib src  `map_a₆`, `def map`, `@[simps]` on `map`, `map_a` in `Mathlib/AlgebraicGeometry/EllipticCurve/` — **HITS**: `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230` `@[simps] def map … := ⟨f W.a₁, …, f W.a₆⟩`; the `@[simps]` attribute auto-generates `WeierstrassCurve.map_a₁ … map_a₆` (used by name in `simp only [b₆, map_a₃, map_a₆]` at line 254 and in `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean:82` `simp only [baseChange, …, map_a₆]`). Also **HIT** `Mathlib/Data/Int/Cast/Lemmas.lean:336` `RingHom.eq_intCast (f : F) (n : ℤ) : f n = n` for `[RingHomClass F ℤ α]` — gives `algebraMap ℤ ℚ B = (B:ℚ)`.
[E] Name pattern      grep project + mathlib for `shortCurveQ_a₆` — exists only at the declaring site; the *general* counterpart `WeierstrassCurve.map_a₆` exists upstream.

Searched for both:
  - the user's current form (`(shortCurveQ A B).a₆ = (B:ℚ)`) — not in mathlib (project-specific, as expected).
  - the literature-standard / general form (`(W.map f).a₆ = f W.a₆`) — **IN MATHLIB as `WeierstrassCurve.map_a₆`** (`@[simps]`-generated, `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`).

Concluded: **found building blocks** — `WeierstrassCurve.map_a₆` (the general functoriality lemma, already `@[simp]`) + `RingHom.eq_intCast` / `map_intCast` (the ℤ→ℚ algebra-map = int-cast identity, already `@[simp]`); their composition yields the project's form. The general form is in mathlib; the specialisation is not (and should not be — it's project glue).

---

### Call sites — `shortCurveQ_a₆`

Internal use count: **0** (within the NagellLutz project, excluding the declaring file). A grep for `shortCurveQ_a₆`, `shortCurveQ_a₄`, `shortCurveQ_a₁` across all `projects/**/*.lean` returned **zero** matches outside `ShortWeierstrass.lean`. A broader grep for any `shortCurveQ` usage shows it is consumed downstream (`Main.lean:36/49/67`, `GeneralMain.lean:154/171`) but **only via `shortCurveQ_equation_iff`** and as a curve argument to `.toAffine.Nonsingular` — never via the per-coefficient projection lemmas.
External-to-file callers: 0 distinct files reference the coefficient lemmas.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none)           | no caller invokes `shortCurveQ_a₆` (or any `shortCurveQ_aᵢ`) by name |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `shortCurveQ_a₆`?):
  - `shortCurveQ_equation_iff` (same file, line 53) expands the equation via `simp [shortCurveQ, shortCurveZ, …]` directly rather than through the coefficient lemmas — i.e. downstream needs go through the *equation* lemma, which unfolds the curve itself, so the coefficient glue is bypassed. (Consistent with the K=0 reading: the coefficient lemmas are `@[simp]` decoration that the actual consumers don't call.)

Call-sites reading: **K = 0, no inline re-derivation via these names.** Per the Phase 6.0.1 table this is the "K = 0, possibly dead `@[simp]` glue" pattern → strong NO-composable / NO-has-it leaning. As `@[simp]` lemmas they may fire silently inside other `simp` calls, but they carry no content beyond what `map_a₆` (also `@[simp]`) + the cast simp set already provide.

---

### Composition check (Phase 6)

Can `shortCurveQ_a₆` be derived from mathlib in ≤3 chained calls?

Attempt 1 (term-mode, 2 rewrites):
```lean
example (A B : ℤ) : (shortCurveQ A B).a₆ = (B : ℚ) := by
  rw [shortCurveQ, WeierstrassCurve.map_a₆]   -- (shortCurveZ A B).a₆ ↦ algebraMap ℤ ℚ ((shortCurveZ A B).a₆); a₆ field = B by rfl
  exact map_intCast (algebraMap ℤ ℚ) B        -- algebraMap ℤ ℚ B = (B : ℚ)   (or: RingHom.eq_intCast / `simp`)
```
  - Mathlib decls used: `WeierstrassCurve.map_a₆`, `map_intCast` (equivalently `RingHom.eq_intCast` / `eq_intCast`).
  - Result: **succeeds**. `(shortCurveZ A B).a₆ = B` is `rfl` (structure projection), so after `map_a₆` the goal is `algebraMap ℤ ℚ B = (B:ℚ)`, closed by the int-cast identity.
  - Notes: this is exactly what the existing proof `by simp [shortCurveQ, shortCurveZ]` does internally — `simp` unfolds `shortCurveQ`, fires the `@[simp]` `map_a₆`, and discharges the int-cast with its `@[simp]` cast lemmas. The whole thing is a `simp` one-liner at any call site.

Conclusion: **COMPOSABLE** (≤3 mathlib calls; in practice a single `simp [shortCurveQ, shortCurveZ]` or even `simp` once `map_a₆` is in scope).

---

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveQ_a₆`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the concept is functoriality of Weierstrass base change; the general form `(W.map f).a₆ = f W.a₆` is universally standard and the top WebSearch hit is Mathlib's own docs page for it.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a triple specialisation (fixed curve, fixed ring map ℤ→ℚ, RHS rewritten via int-cast) of the general lemma; the general form is already upstream, so "generalise-first" would just reproduce an existing decl.
- Mathlib search (Phase 5): found building blocks — `WeierstrassCurve.map_a₆` (`Weierstrass.lean:230`, `@[simps]`-generated, `@[simp]`) and `RingHom.eq_intCast`/`map_intCast` (`Int/Cast/Lemmas.lean:336`, `@[simp]`).
- Composition check (Phase 6): COMPOSABLE in 2 steps; in practice a single `simp`.

**Rationale:**

`shortCurveQ_a₆` carries no mathematical content beyond mechanically composing two lemmas mathlib already has — and both are already `@[simp]`. Mathlib's `WeierstrassCurve.map` is annotated `@[simps]`, which auto-generates `WeierstrassCurve.map_a₆ : (W.map f).a₆ = f W.a₆`; this is the entire general fact. Specialising to `W = shortCurveZ A B` is `rfl` on the structure field (so `(shortCurveZ A B).a₆ = B`), and rewriting `algebraMap ℤ ℚ B` to `(B : ℚ)` is the canonical ℤ-initiality identity `RingHom.eq_intCast`/`map_intCast`. The existing proof `by simp [shortCurveQ, shortCurveZ]` is exactly this composition fired by `simp`. Mathlib does not want a per-coefficient projection lemma about a *specific project-local curve* (`shortCurveQ`); the general `map_a₆` is the right level, and it is already there.

The call-site evidence reinforces this: across the whole NagellLutz project the lemma (and all four siblings `shortCurveQ_a₁…a₄`) has **zero** named call sites. Downstream consumers of `shortCurveQ` go exclusively through `shortCurveQ_equation_iff` (which unfolds the curve directly) — they never invoke the coefficient lemmas. The lemmas are `@[simp]` decoration whose content is already covered by upstream `@[simp]` lemmas (`map_a₆` + the cast simp set), so they are at best redundant local glue.

WHY not (refactor-actionable):
Mathlib has the building blocks; the project's form is a ≤2-call composition. The building blocks are:
- `WeierstrassCurve.map_a₆` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230` (generated by `@[simps]` on `def map`); statement `(W.map f).a₆ = f W.a₆`, already `@[simp]`.
- `map_intCast` / `RingHom.eq_intCast` — `Mathlib/Data/Int/Cast/Lemmas.lean:336`; statement `f (n : ℤ) = (n : α)` for `[RingHomClass F ℤ α]` (the canonical `algebraMap ℤ ℚ` is the int-cast ring hom), already `@[simp]`.

Mathlib building blocks: `WeierstrassCurve.map_a₆`, `map_intCast` (≡ `RingHom.eq_intCast`).
Composition sketch (≤3 lines):
```lean
example (A B : ℤ) : (shortCurveQ A B).a₆ = (B : ℚ) := by
  rw [shortCurveQ, WeierstrassCurve.map_a₆]; exact map_intCast (algebraMap ℤ ℚ) B
-- or simply:  by simp [shortCurveQ, shortCurveZ]   (the current proof — map_a₆ + cast are @[simp])
```
Call sites in our project (from Phase 6.0): **K = 0** (no named uses; downstream uses `shortCurveQ_equation_iff` instead).
Refactor plan: because K = 0, there are no call sites to rewrite. Options, in order of preference:
  1. **Delete** `shortCurveQ_a₆` (and likely the siblings `shortCurveQ_a₁…a₄`, plus possibly the ℤ-side `shortCurveZ_aᵢ` if equally unused) — nothing in the project invokes them by name, and `simp` already has `map_a₆` + cast lemmas, so any future `simp` that needs the coordinate gets it for free after unfolding `shortCurveQ`/`shortCurveZ`.
  2. If a future proof *does* want the coordinate as a stated rewrite, inline `simp [shortCurveQ, shortCurveZ]` (or `simp [shortCurveQ, shortCurveZ, map_a₆]`) at that one call site rather than keeping a named lemma.
Caveat for the cleaner: these are `@[simp]`; before deleting, confirm via a build that no *other* file's `simp` silently relies on them (the K=0 grep says no named use, but `@[simp]` lemmas fire anonymously). Given the upstream `@[simp] map_a₆` + cast set produce the same normal form, removal should be simp-neutral — but verify on green. This is a CLEANUP action (dedup/inline against mathlib), not a dev-ticket; it changes no statement and adds no sorry.

Next action: delete `shortCurveQ_a₆` from the project (sweep the four sibling `shortCurveQ_aᵢ` lemmas in the same pass); rely on mathlib's `@[simp] WeierstrassCurve.map_a₆` + int-cast simp lemmas, unfolding `shortCurveQ`/`shortCurveZ` where a coordinate is needed. Verify `lake build` stays green and `#print axioms` is unchanged.

---

## Next step

Delete `shortCurveQ_a₆` (and the sibling coefficient lemmas in the same sweep) and inline `simp [shortCurveQ, shortCurveZ]` where a coefficient is needed — mathlib's `@[simp] WeierstrassCurve.map_a₆` plus the int-cast `@[simp]` lemmas already produce this normal form. K = 0 call sites, so no rewrites are needed; confirm on a green build that no anonymous `@[simp]` dependence breaks.
