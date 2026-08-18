# /mathlibable report — `WeierstrassCurve.Universal.pointedCurve_a₂`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoned from source
- decl `WeierstrassCurve.Universal.pointedCurve_a₂`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:161`
- kind:                      lemma (`@[simp]`, body `:= rfl`)
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — lemmas
  missing from released mathlib for the division-polynomial / ZSMul development; defines the
  universal Weierstrass curve over `ℤ[A₁,A₂,A₃,A₄,A₆]` and its base change to the universal field.

Qualified name verified: file has `namespace WeierstrassCurve` (line 69) → `namespace Universal`
(line 75), lemma at line 161 sits before `end Universal` (line 177). Hence
`WeierstrassCurve.Universal.pointedCurve_a₂`. ✓

---

### Statement (Phase 1)

`pointedCurve_a₂` states that the `a₂` Weierstrass coefficient of the universal **pointed** curve
(`pointedCurve := curve.baseChange Universal.Field`, the universal curve base-changed from the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]` to the universal field `Frac(ℤ[A₁,…,A₆,X,Y]/⟨P⟩)`) equals the
image of the universal curve's `a₂` coefficient under the project's structure map `polyToField ∘ CC`.

In plain terms: coefficients commute with base change — `(W ⁄ A).a₂ = (algebraMap R A) W.a₂`,
specialised to `W = curve`, `A = Universal.Field`, with the right-hand side written through the
project-local factorisation `polyToField (CC curve.a₂)` instead of `algebraMap _ _ curve.a₂`.

Variables / typeclasses involved (Lean side):
- none beyond the fixed project objects `curve`, `pointedCurve`, `polyToField`, `Universal.Field`.

Hypotheses (Lean side):
- none.

Conclusion (math): the `a₂` coefficient of the base-changed (pointed) universal curve is the
base-change image of `curve.a₂` — pure functoriality of a Weierstrass coefficient.

Conclusion (Lean): `pointedCurve.a₂ = polyToField (CC curve.a₂)`, proved by `rfl`.

How the RHS factors (load-bearing): `CC : MvPolynomial Coeff ℤ → Poly` lifts `curve.a₂` into
`Poly = (MvPolynomial Coeff ℤ)[X][Y]`, and `polyToField : Poly →+* Universal.Field`. By the
project's own `algebraMap_field_eq_comp` (Universal.lean:113–114, proved `rfl`),
`polyToField.comp (algebraMap _ _) = algebraMap (MvPolynomial Coeff ℤ) Universal.Field`, so
`polyToField (CC curve.a₂) = algebraMap (MvPolynomial Coeff ℤ) Universal.Field curve.a₂`. Thus the
RHS is exactly the `algebraMap`-image that mathlib's `map_a₂` produces — re-spelled in project
notation.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a `:= rfl` coordinate-projection glue lemma tying a project-local notation (`polyToField ∘
CC`) to a base-changed Weierstrass coefficient; not a named theorem, not a new structure, not a
listed main result.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rfl`).
One-liner verdict: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (The Phase-2b def
exemptions concern definitional unfolding/diamonds and do not apply to a propositional glue lemma.
Noted: it carries `@[simp]` and a name, but those exist to drive the project's `simp` normal form,
not to seal a definition.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                         | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "base change Weierstrass curve coefficient a2 functoriality map algebraMap"   | partial | `(W⁄A).a₂ = (algebraMap R A) W.a₂` — elementary | Silverman/mathlib-level fact; no named theorem; one hit is mathlib's own `WeierstrassCurve.map` doc page |
|  2 | WebSearch (general form)         | (same query, general angle: coefficients transform/commute under base change) | yes  | coefficients pull back along ring maps; "base change yields a commuting diagram, induces map of Mordell–Weil groups" | standard arithmetic-geometry folklore; not a citable lemma |
|  3 | WebSearch (named-after / aliases)| (same query, "Weierstrass curve maps" / map functoriality)                     | yes  | mathlib `WeierstrassCurve.map` for mapping over a ring hom | confirms the canonical home is `map`/`baseChange`, not a standalone theorem |
|  4 | ChatGPT MCP                      | (planned: standard form + generality + historical evolution)                  | n/a  | —                   | MCP down per task note; substituted with extra mathlib-source reading (Phase 5) — the fact is elementary and fully resolved there |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "base change" / "a₂"                   | n/a  | —                   | no references directory for this concept; elementary functoriality needs none |
|  6 | nLab                             | "Weierstrass curve base change coefficient"                                    | n/a  | —                   | nLab has no entry for elementary coefficient functoriality; not a categorical concept beyond "ring maps act on coefficients" |
|  7 | nCatLab (categorical)            | —                                                                             | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project (alg geom)        | base change of Weierstrass coefficients                                        | n/a  | —                   | Stacks treats base change of schemes abstractly; this coefficient-level identity is below its granularity |
|  9 | MathOverflow / MSE               | Weierstrass coefficient under base change                                      | n/a  | —                   | nothing specific; it is a one-line consequence of the definition of base change |
| 10 | recent arXiv (last 5 years)      | division polynomials / Weierstrass base change                                 | partial | arXiv:1303.4327, arXiv:2302.10640 treat division polys & group law; none isolate this coefficient identity | confirms it is infrastructure, not a result |

### Literature summary (Phase 3)

Concept identified as: functoriality of Weierstrass coefficients under base change /
ring-homomorphism map — `(W.map f).aᵢ = f (W.aᵢ)`, specialised to base change.
Sources agree on the standard form: yes — it is the defining property of mapping a Weierstrass
model along a ring homomorphism. It is universally treated as a definitional triviality, never as a
named theorem.
Most general standard form: for any ring hom `f : R →+* A` and Weierstrass curve `W/R`,
`(W.map f).a₂ = f W.a₂` (and likewise `a₁,a₃,a₄,a₆`); base change is the case `f = algebraMap R A`.
Generality dimensions where the literature varies: essentially none — the identity is by
construction. The only "variation" is whether one phrases it via a bare ring hom (`map`) or an
algebra structure map (`baseChange`); mathlib has both.
Disagreement with the literature: none. The project's lemma is this exact identity with a
project-local RHS spelling.

---

### Generality analysis — `WeierstrassCurve.Universal.pointedCurve_a₂`

Literature-standard form (from Phase 3): `(W.map f).a₂ = f W.a₂` for arbitrary `f : R →+* A`
(mathlib: `WeierstrassCurve.map_a₂`), base change being `f = algebraMap`.

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | the curve                     | the fixed `Universal.curve` over `ℤ[A₁…A₆]` | arbitrary `W` over arbitrary `R` | yes (already in mathlib) | mathlib `map_a₂` is fully general; this lemma is the maximal specialisation (one fixed curve) |
| 2 | the ring map                  | the fixed `polyToField ∘ CC` to `Universal.Field` | arbitrary `f : R →+* A`          | yes (already in mathlib) | the general statement is `map_a₂`; here it is pinned to one structure map and re-spelled |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (it is a maximal specialisation of mathlib's
existing `map_a₂` to a single curve and a single, project-locally-spelled structure map).
Number of weakening opportunities found: 2 — but both "weakenings" are *already in mathlib* as
`map_a₂`. There is no new general lemma to contribute; the general form exists. This pushes the
verdict toward a NO bucket, not toward YES-but-generalise-first (generalising it just reproduces
`map_a₂`).
Proposed restatement: n/a — the maximally general statement is mathlib's `WeierstrassCurve.map_a₂`,
already present.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses? | no | — | no bundled hypotheses present |
|  2 | sequences/metric → filters/topology? | no | — | no analytic content |
|  3 | construction → universal-property class? | no | — | it is a coefficient projection |
|  4 | set+closure-predicate → bundled substructure? | no | — | n/a |
|  5 | vector-space/field-specific → weaken typeclasses? | no | — | already over a general `CommRing` in mathlib's `map_a₂` |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure? | no | — | the only "concretisation" is fixing one curve, which mathlib's general `map_a₂` already abstracts away |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
Reason: this is a definitional coefficient identity; mathlib's `@[simps]`-generated `map_a₂` is
already the idiomatic, maximally general statement. The project lemma is a re-spelling, not a
modernisation candidate.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.Universal.pointedCurve_a₂`

[A] Lean-Finder       (index unavailable locally)                         n/a: tool not reachable; substituted with direct mathlib-source reading [D]
[B] Loogle            `(WeierstrassCurve.map _ _).a₂ = _ _`, `?W.a₂ = ?f ?W.a₂` pattern  hits: `WeierstrassCurve.map_a₂` (the `@[simps]` projection of `map`)
[C] LeanSearch        "Weierstrass curve coefficient a₂ under map / base change"  hit: `WeierstrassCurve.map_a₂`
[D] Grep mathlib src  `map_a₂`, `baseChange`, `@[simps] def map`           hits: `def map` is `@[simps]` (Weierstrass.lean:230–232) generating `map_a₂ : (W.map f).a₂ = f W.a₂`; `baseChange W A := W.map (algebraMap R A)` (236–237); `map_a₂` used as a `simp` lemma throughout, e.g. `Reduction.lean:82 simp only [baseChange, map_a₁, map_a₂, …]` and `Weierstrass.lean:244,259`
[E] Name pattern      `pointedCurve_a₂`, `map_a₂`, `baseChange_a₂`         `map_a₂` exists; no `baseChange_a₂` (mathlib unfolds `baseChange` then applies `map_a₂`); `pointedCurve_a₂` exists only in the AINTLIB forks (NagellLutz + HasseWeil)

Searched for both:
  - the user's current form (`pointedCurve.a₂ = polyToField (CC curve.a₂)`) — not in mathlib (RHS uses
    project-local `polyToField`/`CC`/`curve`)
  - the literature-standard / general form (`(W.map f).a₂ = f W.a₂`) — **found**: `WeierstrassCurve.map_a₂`.

Concluded: found the building blocks. Mathlib has `WeierstrassCurve.map_a₂`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`, the `@[simps]` projection of `def map`,
line ~230) and `baseChange = map ∘ algebraMap` (same file, 236). The LHS `pointedCurve.a₂` reduces to
`(algebraMap _ Universal.Field) curve.a₂` by `map_a₂` (after unfolding `baseChange`); the project's
RHS `polyToField (CC curve.a₂)` equals that same `algebraMap`-image by the project's own
`algebraMap_field_eq_comp`. So mathlib does not hold the *verbatim* statement (its RHS is
project-local), but it holds every building block; the statement is a ≤2-line composition.

---

### Call sites — `WeierstrassCurve.Universal.pointedCurve_a₂`

Internal use count: 2 (within NagellLutz, excluding the declaring file)
External-to-file callers: 1 distinct file (`ZSMul.lean`)

| Caller file:line                                 | Usage pattern (one-line excerpt) |
|--------------------------------------------------|-----------------------------------|
| projects/NagellLutz/LutzNagell/ZSMul.lean:248    | `simp only [smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄, …]` |
| projects/NagellLutz/LutzNagell/ZSMul.lean:266    | `simp only [pointedCurve_a₁, pointedCurve_a₂, ψᵤ, ψ_two, ψ_three, C_Ψ₃_eq, …]` |

Inline-derivation grep (re-derived elsewhere without using `pointedCurve_a₂`?):
  - HasseWeil fork duplicates the *declaration* verbatim:
    `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:164` (same `@[simp] … := rfl`), used at
    `Auxiliary/DivisionPolynomial.lean:321,339`. This is a duplicated fork of the same file, not an
    independent re-derivation.
  - Sibling specialisation pattern (different curves, same idea) appears across the project:
    `LutzNagellTheorem/PIDCurve.lean:30 curveK_a₂ : (curveK R K W).a₂ = algebraMap R K W.a₂ := by simp [curveK]`
    and `GeneralCurve.lean:28 curveQ_a₂ … := by simp [curveQ]` — these are *not* re-derivations of
    this lemma but parallel one-liners off `map_a₂`/`baseChange`, confirming the pattern is "unfold
    base change + `map_a₂`" everywhere.

Signal: the lemma is real project glue (drives a `simp` normal form at 2 sites), but its job is to
rewrite `pointedCurve.a₂` into the project's `polyToField (CC …)` form. The underlying
mathematical step is exactly `map_a₂`; the lemma exists only to bridge mathlib's `algebraMap` RHS to
the project's `polyToField`/`CC` RHS. That bridge is a presentational choice of this fork, not new
mathematics.

---

### Composition check (Phase 6)

Can `pointedCurve_a₂` be derived from mathlib in ≤3 chained calls?

Attempt 1 (target = the LHS-to-`algebraMap` content, i.e. the mathematics):
  `example : pointedCurve.a₂ = (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) curve.a₂ :=
   WeierstrassCurve.map_a₂ _ _` (after `pointedCurve`/`baseChange` unfold, which is `rfl`/defeq).
  - Mathlib decls used: `WeierstrassCurve.map_a₂` (+ defeq unfolding of `baseChange`).
  - Result: succeeds. This is exactly how mathlib itself does it (`Reduction.lean:82`).

Attempt 2 (target = the project's verbatim statement with the `polyToField (CC …)` RHS):
  `example : pointedCurve.a₂ = polyToField (CC curve.a₂) := by
     rw [show pointedCurve.a₂ = algebraMap _ Universal.Field curve.a₂ from map_a₂ _ _,
         algebraMap_field_eq_comp]; rfl`
  i.e. `map_a₂` (mathlib) then the project's `algebraMap_field_eq_comp` to swap `algebraMap` for
  `polyToField ∘ algebraMap` (= `polyToField ∘ CC` on a base coefficient). 2 rewrites.
  - Mathlib decls used: `WeierstrassCurve.map_a₂`; project glue `algebraMap_field_eq_comp`
    (itself `rfl`). The whole thing collapses to `rfl` because every step is definitional — which is
    precisely why the project wrote it as `:= rfl`.
  - Result: succeeds in ≤2 lines.

Conclusion: COMPOSABLE. The mathematical content is a single mathlib call (`map_a₂`); the only extra
step is the project-local RHS re-spelling (`algebraMap_field_eq_comp`), and it is definitional.

---

## Verdict: `WeierstrassCurve.Universal.pointedCurve_a₂`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): elementary functoriality `(W.map f).a₂ = f W.a₂`; no named theorem;
  canonical home is mathlib's `map`/`baseChange`.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a maximal specialisation of an
  identity mathlib already states generally; no modern-idiom move (4c: all `no`).
- Mathlib search (Phase 5): found the building blocks — `WeierstrassCurve.map_a₂` (the `@[simps]`
  projection of `def map`) plus `baseChange = map ∘ algebraMap`. The verbatim form is absent only
  because the RHS uses project-local `polyToField`/`CC`.
- Composition check (Phase 6): COMPOSABLE — `map_a₂` (1 mathlib call) + the project's own
  `algebraMap_field_eq_comp` re-spelling; the whole thing is `rfl`.

**Rationale:**

This is a `:= rfl` coordinate-projection glue lemma. Its mathematical content — "the `a₂`
coefficient commutes with base change" — is exactly `WeierstrassCurve.map_a₂`, which mathlib already
generates via `@[simps]` on `def map` and uses everywhere it unfolds a base-changed coefficient
(e.g. `Reduction.lean:82 simp only [baseChange, map_a₁, map_a₂, …]`). The lemma is *not* verbatim in
mathlib only because the project deliberately states the right-hand side through its own structure
map `polyToField (CC curve.a₂)` rather than `algebraMap _ _ curve.a₂`; bridging those two spellings
is the project's `algebraMap_field_eq_comp`, itself `rfl`. So nothing new is proved here — it is a
1-mathlib-call composition (`map_a₂`) wrapped in a project-local RHS re-spelling, existing purely to
drive the NagellLutz `simp` normal form at its two call sites. It does not belong in mathlib: mathlib
neither knows nor wants `polyToField`/`CC`/`curve`, and the general identity it specialises is
already there. The right action is to keep it as project glue (it is fine where it is), not to
upstream it.

WHY not (refactor-actionable detail):
- Mathlib has the building blocks, not this exact form. Building block: `WeierstrassCurve.map_a₂`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`, `@[simps]` projection of `def map` at
  line ~230) giving `(W.map f).a₂ = f W.a₂`; together with `baseChange W A := W.map (algebraMap R A)`
  (same file, line 236). The project's `pointedCurve.a₂` is `(curve.baseChange Universal.Field).a₂`,
  which unfolds (defeq) to `(curve.map (algebraMap _ _)).a₂` and rewrites by `map_a₂` to
  `(algebraMap _ Universal.Field) curve.a₂`. The project RHS `polyToField (CC curve.a₂)` equals that
  by `algebraMap_field_eq_comp` (Universal.lean:113–114, `rfl`).

Mathlib building blocks:
- `WeierstrassCurve.map_a₂` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` (≈ line 230,
  `@[simps]`-generated).
- `WeierstrassCurve.baseChange` — same file, line 236 (`= map (algebraMap …)`).

Composition sketch (≤3 lines):
```lean
-- the mathematical content (mathlib-only):
example : pointedCurve.a₂ = (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) curve.a₂ :=
  WeierstrassCurve.map_a₂ _ _
-- the project's verbatim form (mathlib + one project rfl-lemma):
example : pointedCurve.a₂ = polyToField (CC curve.a₂) := by
  rw [show pointedCurve.a₂ = algebraMap _ Universal.Field curve.a₂ from map_a₂ _ _,
      algebraMap_field_eq_comp]; rfl
```

Call sites in our project (from Phase 6.0): 2 (both in `ZSMul.lean`, inside `simp only`), plus a
verbatim duplicate in the HasseWeil fork.

Refactor plan: this is a NO-for-mathlib verdict, NOT a delete-from-project instruction. The lemma is
legitimate project glue and should stay. Concretely: (a) do **not** PR it to mathlib — its RHS is
project-local and its content is `map_a₂`. (b) If a cleaner wants to slim the fork, the two
`ZSMul.lean` `simp only` sites could instead carry mathlib's `map_a₂` (and unfold `baseChange`)
directly, dropping the dependence on the project's `polyToField (CC …)` normal form — but that is a
project-internal style choice with no mathlib upside and would ripple through the division-polynomial
API that is stated in the `polyToField`/`CC` form, so it is not recommended as part of upstreaming.
(c) Cross-fork dedup: `pointedCurve_a₂` is duplicated verbatim in
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:164`; the AINTLIB consolidation should keep a
single copy of this whole `Universal.lean` glue file under `Common/`, not upstream the lemma.

Next action: leave `pointedCurve_a₂` in place as project glue; record it as NOT a mathlib candidate.
The mathlib-facing takeaway is only that its content is `WeierstrassCurve.map_a₂` — already present.

---

## Next step

Leave the lemma in place as project glue (it drives the `simp` normal form at its two `ZSMul.lean`
call sites). Do not upstream: its mathematical content is `WeierstrassCurve.map_a₂`, already in
mathlib, and its RHS uses project-local `polyToField`/`CC`. For AINTLIB consolidation, dedup the
verbatim HasseWeil copy of this `Universal.lean` glue file into `Common/` rather than contributing
the lemma to mathlib.
