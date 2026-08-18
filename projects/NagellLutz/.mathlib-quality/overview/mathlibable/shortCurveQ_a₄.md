## /mathlibable report — `LutzNagell.LutzNagellTheorem.shortCurveQ_a₄`

### Baseline (Phase 0)
- lake build:               (not run — local build stale per task; reasoning from source)
- decl `LutzNagell.LutzNagellTheorem.shortCurveQ_a₄`:  ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean:47`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Sets up the short Weierstrass curve `y² = x³ + A·x + B` over ℤ and its base change to ℚ, with basic rewriting lemmas (coefficients, equation, discriminant).

True qualified name confirmed from source: namespaces `LutzNagell` then `LutzNagellTheorem`, base name `shortCurveQ_a₄`. The task's parenthetical guess matches.

### Statement (Phase 1)

`shortCurveQ_a₄` states: for integers `A B`, the `a₄` coefficient of the short Weierstrass curve `shortCurveQ A B` over ℚ equals the rational `(A : ℚ)`.

Here `shortCurveQ A B := (shortCurveZ A B).map (algebraMap ℤ ℚ)`, the base change to ℚ of the ℤ-curve `shortCurveZ A B = ⟨a₁=0, a₂=0, a₃=0, a₄=A, a₆=B⟩`. The lemma is tagged `@[simp]`.

Variables / typeclasses involved (Lean side):
- `A B : ℤ` — the two short-Weierstrass coefficients (everything else fixed at 0).

Hypotheses (Lean side): none.

Conclusion (math): the `x`-linear coefficient of the ℚ-base-change is the image of `A` under ℤ ↪ ℚ.
Conclusion (Lean): `(shortCurveQ A B).a₄ = (A : ℚ)`.

Proof body: `by simp [shortCurveQ, shortCurveZ]`. This closes only because mathlib's `@[simp]`-tagged `WeierstrassCurve.map_a₄` rewrites `((shortCurveZ A B).map (algebraMap ℤ ℚ)).a₄` to `(algebraMap ℤ ℚ) (shortCurveZ A B).a₄`, then the project's `shortCurveZ_a₄` (also a `@[simp]` `rfl` lemma) and the `algebraMap ℤ ℚ = Int.cast` simp fact finish it.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a coefficient-projection rewriting lemma about a project-specific `def` (`shortCurveQ`); not a named theorem, not a `## Main result`, introduces no new structure. (Literature width still treated as exhaustive below; the concept is fully standard.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner def check is n/a. (For the record the proof is a single `simp` line, which reinforces triviality, but Phase 2b targets definitions.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | mathlib WeierstrassCurve map coefficients a4 base change simp lemma                             | partial | mathlib `WeierstrassCurve` docs (Weierstrass.html) | confirms the curve struct + map/base-change API exists; no math-literature "theorem" because this is bookkeeping, not mathematics |
|  2 | WebSearch (general form)         | (subsumed) functoriality of Weierstrass coefficients under ring homomorphism                   | n/a  | — | "coefficients of a base-changed curve are the images of the coefficients" is a definitional triviality, not a literature result |
|  3 | WebSearch (named-after/aliases)  | (subsumed) Silverman short Weierstrass form coefficients                                        | n/a  | $y^2 = x^3 + Ax + B$ standard (Silverman AEC III.1) | the SHORT FORM is standard literature; the *coefficient-readoff lemma* is not a literature object |
|  4 | ChatGPT MCP                      | (MCP down per task; reasoned from source instead)                                              | n/a  | — | fallback used; the statement is a definitional projection, no historical evolution to track |
|  5 | Local references                 | `.mathlib-quality/references/` for "Weierstrass coefficient map"                                | n/a  | — | references dir not consulted for a definitional bookkeeping lemma; nothing in the literature to match |
|  6 | nLab                             | Weierstrass curve / elliptic curve coefficients                                                 | n/a  | — | nLab treats elliptic curves abstractly; no per-coefficient base-change lemma |
|  7 | nCatLab                          | —                                                                                              | n/a  | — | not a categorical concept |
|  8 | Stacks Project                   | elliptic curve Weierstrass equation base change                                                 | n/a  | — | Stacks has elliptic-curve theory but no `aᵢ`-coefficient-of-map lemma; this is mathlib-internal bookkeeping |
|  9 | MathOverflow / MSE               | —                                                                                              | n/a  | — | no research-level question; trivial |
| 10 | recent arXiv (last 5 yrs)        | —                                                                                              | n/a  | — | not a research result |

### Literature summary (Phase 3)

Concept identified as: the `a₄` coefficient of the short Weierstrass model `y² = x³ + Ax + B` (Silverman, *Arithmetic of Elliptic Curves*, III.1) read off after base change ℤ → ℚ.
Sources agree on the standard form: yes — the short Weierstrass equation is universally `y² = x³ + Ax + B`; `a₄ = A`, `a₆ = B`, `a₁ = a₂ = a₃ = 0`.
Most general standard form: the statement that ring homomorphisms act coefficient-wise on Weierstrass data — i.e. `(map f W).aᵢ = f (W.aᵢ)` — is a definitional fact, not a named theorem.
Generality dimensions where the literature varies: none of substance. The mathematical content ("base change sends `a₄` to its image") is the *definition* of base change; the literature never isolates it as a lemma.
Disagreement with the literature: none. This is bookkeeping that supports the standard short form.

### Generality analysis — `shortCurveQ_a₄`

Literature-standard / mathlib-general form (from Phase 3 + Phase 5): `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄`, for any `CommRing R`, `CommRing A`, ring hom `f : R →+* A`, and arbitrary curve `W`.

| # | Parameter / hypothesis        | Current Lean form                         | Literature/mathlib-general form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | the curve                     | the specific `shortCurveZ A B` (3 coeffs zero) | arbitrary `W : WeierstrassCurve R`  | yes (already in mathlib) | mathlib's `map_a₄` is stated for ALL curves; ours fixes `a₁=a₂=a₃=0`, `a₄=A`, `a₆=B` |
| 2 | the ring map                  | `algebraMap ℤ ℚ` specifically             | arbitrary `f : R →+* A`                  | yes (already in mathlib) | nothing uses ℤ→ℚ specifically; mathlib's `map_a₄` is hom-generic |
| 3 | source/target rings           | `ℤ → ℚ`                                    | any `CommRing → CommRing`                | yes (already in mathlib) | the coefficient read-off is ring-agnostic |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (it is a triple specialisation — fixed curve, fixed map, fixed rings — of mathlib's already-existing `WeierstrassCurve.map_a₄`).
Number of weakening opportunities found: 3 (curve, map, rings) — but all three are ALREADY realised by an existing mathlib lemma, so this is not a "generalise-and-upstream" situation; it is a "mathlib already has the general lemma" situation.
Proposed restatement: none needed — the general lemma `WeierstrassCurve.map_a₄` already exists in mathlib.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled-hyp → typeclass? | no | — | no hypotheses |
| 2 | sequences/metric → filters? | no | — | algebraic, no topology |
| 3 | construct → universal property? | no | — | a coefficient projection |
| 4 | set+closure → bundled substructure? | no | — | n/a |
| 5 | vector-space/field-specific → weaker typeclass? | no | mathlib's `map_a₄` is already `CommRing`-generic | already maximally weak |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index (ℤ,ℚ) → arbitrary structure? | yes | already done by `map_a₄` over `R →+* A` | the modern/general form is the existing mathlib lemma |

Modern idiom available: no (the "modern idiom" — `map_a₄` for an arbitrary ring hom — already exists in mathlib; nothing to add).
One-line reason this is not a modernisation move: the maximally-general, idiomatic form is already in mathlib as `WeierstrassCurve.map_a₄`; the project lemma is a downstream specialisation of it.

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma`.

### Mathlib search-status: `LutzNagell.LutzNagellTheorem.shortCurveQ_a₄`

[A] Lean-Finder       (index unavailable locally)                                     n/a: tool not reachable
[B] Loogle            `?W.map ?f |>.a₄` / coefficient-of-map pattern                   HIT — `WeierstrassCurve.map_a₄`
[C] LeanSearch        "a4 coefficient of mapped Weierstrass curve"                     HIT — same
[D] Grep mathlib src  `map_a₄`, `def map`, `@[simps]` in EllipticCurve/Weierstrass.lean  HIT — `def map` at Weierstrass.lean:230 carries `@[simps]`, auto-generating `map_a₄`; used at Reduction.lean:82, Weierstrass.lean:249/259
[E] Name pattern      `map_a₄` / `IsShortNF` in NormalForms.lean                       HIT — `map_a₄` exists; also `WeierstrassCurve.IsShortNF` (NormalForms.lean:185) provides `a₁,a₂,a₃ = 0` and short-form `Δ` (matching this file's `shortCurveZ_delta`)

Searched for both:
  - the user's current form `(shortCurveQ A B).a₄ = (A : ℚ)` — no verbatim hit (it bakes in the specific curve + cast);
  - the literature/mathlib-general form `(W.map f).a₄ = f W.a₄` — HIT, `WeierstrassCurve.map_a₄` (generated by `@[simps]` on `WeierstrassCurve.map`, located in `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`).

Concluded: "found building blocks (`WeierstrassCurve.map_a₄`, the project-local `shortCurveZ_a₄`, and `algebraMap ℤ ℚ = Int.cast`); composition yields our form in one `simp`." The general lemma `map_a₄` IS in mathlib; the project's `(A : ℚ)` RHS additionally requires the project's own `shortCurveZ_a₄` and the cast simp, so it is a 1–3 call composition rather than a verbatim mathlib hit.

### Call sites — `LutzNagell.LutzNagellTheorem.shortCurveQ_a₄`

Internal use count: 0  (grep over the whole project finds the name ONLY on its own definition line, ShortWeierstrass.lean:47)
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | — |

Inline-derivation grep: the parent def `shortCurveQ` IS used downstream (`Main.lean:36/49/67`, `GeneralMain.lean:154`) via `(shortCurveQ A B).toAffine.Nonsingular x y`. Those consumers may pick up `shortCurveQ_a₄` implicitly through `simp` (it is `@[simp]`), but there is no explicit `shortCurveQ_a₄` reference and no re-derivation of the `a₄ = A` fact by hand — when needed it would be discharged by `map_a₄` + `shortCurveZ_a₄` anyway.

Signal: K = 0 explicit internal uses; it is a `@[simp]` convenience lemma feeding the simp set. Per the call-sites table this is a "wrapper consumers reach only through `simp`" pattern, reinforcing NO-composable.

### Composition check (Phase 6)

Can `shortCurveQ_a₄` be derived from mathlib (+ the two project `rfl` lemmas it sits beside) in ≤3 chained calls?

Attempt 1: `(WeierstrassCurve.map_a₄ ..).trans (by simp [shortCurveZ])`, i.e.
  - `simp only [shortCurveQ, WeierstrassCurve.map_a₄, shortCurveZ_a₄, map_intCast]` (or just the curve's own `simp` set).
  - Mathlib decls used: `WeierstrassCurve.map_a₄`; the `algebraMap ℤ ℚ a = (a : ℚ)` cast simp (`eq_intCast`/`map_intCast`); plus project `shortCurveZ_a₄`.
  - Result: succeeds — this is literally what the existing one-line proof `simp [shortCurveQ, shortCurveZ]` does (the `@[simp] map_a₄` is the load-bearing step).
  - Notes: ≤3 mathlib ingredients; no new mathematical idea.

Conclusion: COMPOSABLE.

## Verdict: `LutzNagell.LutzNagellTheorem.shortCurveQ_a₄`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the short form `y²=x³+Ax+B` is standard (Silverman III.1), but the coefficient read-off after base change is a definitional triviality, not a literature theorem.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a triple specialisation (fixed curve, fixed map `algebraMap ℤ ℚ`, fixed rings) of mathlib's already-existing general lemma.
- Mathlib search (Phase 5): the general form `WeierstrassCurve.map_a₄` exists in mathlib (auto-generated by `@[simps]` on `WeierstrassCurve.map`, `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`). Mathlib also has `IsShortNF` for the `a₁=a₂=a₃=0` short-form package.
- Composition check (Phase 6): COMPOSABLE — `map_a₄` + the project's `shortCurveZ_a₄` + the `algebraMap ℤ ℚ = Int.cast` simp, exactly the existing one-line proof.

**Rationale:**

This is project-local bookkeeping, not a mathlib candidate. Mathlib already provides the maximally-general statement `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄` for an arbitrary curve over an arbitrary `CommRing` and an arbitrary ring homomorphism `f`, and it is `@[simp]` (generated by `@[simps]` on `WeierstrassCurve.map`). Our lemma is that general lemma specialised to the one curve `shortCurveZ A B` and the one map `algebraMap ℤ ℚ`, with the right-hand side further rewritten through `shortCurveZ_a₄` and the `Int.cast` simp to land on `(A : ℚ)`. The lemma's own proof — a single `simp [shortCurveQ, shortCurveZ]` — closes *only because* `map_a₄` is in the default simp set, which is direct evidence that the content is supplied entirely by mathlib's existing API.

Because the project's `(A : ℚ)` form differs from `map_a₄`'s `f W.a₄` RHS by exactly the project-specific definitions, this is a 1–3 mathlib-call composition rather than a verbatim mathlib hit — hence NO-composable-from-mathlib rather than NO-mathlib-has-it. It has zero explicit call sites (it only ever fires implicitly via `simp`), so there is nothing to protect by keeping a named wrapper.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the project's `(A:ℚ)` form is a ≤3-call composition of them. The blocks are:
- `WeierstrassCurve.map_a₄` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230` (`@[simps]`-generated, `@[simp]`).
- project-local `shortCurveZ_a₄` (ShortWeierstrass.lean:35, `rfl`, `@[simp]`).
- the `algebraMap ℤ ℚ a = (a : ℚ)` cast simp (`eq_intCast` / `map_intCast`).

Mathlib building blocks:      `WeierstrassCurve.map_a₄`  (+ `eq_intCast`/`map_intCast`)
Composition sketch (≤3 lines):
```lean
-- with shortCurveQ and shortCurveZ unfolded, this is exactly the curve's simp set:
example (A B : ℤ) : (shortCurveQ A B).a₄ = (A : ℚ) := by
  simp [shortCurveQ, shortCurveZ]   -- uses WeierstrassCurve.map_a₄ (a @[simp] lemma) + cast simp
```
Call sites in our project (from Phase 6.0):  K = 0 (explicit). Implicit `@[simp]` users only.
Refactor plan: this lemma can be kept as a tiny `@[simp]` convenience shim (cheap, harmless, keeps the project's curve-coefficient simp set self-contained) OR dropped — since downstream files that touch `shortCurveQ` already get `a₄ = A` for free from mathlib's `@[simp] map_a₄` plus `shortCurveZ_a₄`, deleting `shortCurveQ_a₄` (and its `a₁/a₂/a₃/a₆` siblings) and letting `simp` use `map_a₄` directly would not break any explicit caller. Either way it is NOT a mathlib contribution: mathlib's `map_a₄` is the upstream home of this content.
Next action: do not upstream. Leave as a project-local `@[simp]` shim, or inline `simp [shortCurveQ, shortCurveZ, map_a₄]` at the (currently implicit) use sites; no mathlib PR.

---

## Next step

Do not upstream `shortCurveQ_a₄`. Mathlib already owns this content via the general `@[simp]` lemma `WeierstrassCurve.map_a₄`; the project lemma is a ≤3-call specialisation (`map_a₄` + `shortCurveZ_a₄` + the `Int.cast` simp). Keep it as a harmless project-local `@[simp]` shim or inline it; no mathlib PR.
