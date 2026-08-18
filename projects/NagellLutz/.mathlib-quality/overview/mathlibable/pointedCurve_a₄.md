# /mathlibable report — `WeierstrassCurve.Universal.pointedCurve_a₄`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task note; decl elaborates per source)
- decl `WeierstrassCurve.Universal.pointedCurve_a₄`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:163`
  (inside `namespace WeierstrassCurve` → `namespace Universal`, lines 69/75 … 177/243)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" —
  provides lemmas missing from released mathlib for the division-polynomial / ZSMul development;
  defines the universal Weierstrass curve and the universal *pointed* elliptic curve over
  `Frac(ℤ[A₁..A₆,X,Y]/⟨P⟩)`.

NOTE: This decl is **duplicated verbatim** in the forked HasseWeil track at
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:166` (same `:= rfl`). The verdict below
applies to both copies.

---

### Statement (Phase 1)

`pointedCurve_a₄` states the following:

> Let `curve` be the universal Weierstrass curve over `R₀ := MvPolynomial Coeff ℤ = ℤ[A₁,A₂,A₃,A₄,A₆]`
> (so `curve.a₄ = X A₄`, the fourth coefficient variable). Let `pointedCurve := curve.baseChange Universal.Field`
> be its base change to the universal field `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨P⟩)`. Then the `a₄`
> coefficient of `pointedCurve` equals `polyToField (CC curve.a₄)`,

where:
- `CC : R₀ → R₀[X][Y] = Poly` is mathlib's double-constant embedding `CC r = C (C r)`
  (`Mathlib/Algebra/Polynomial/Bivariate.lean:47`);
- `polyToField : Poly →+* Universal.Field` is this project's structure map
  `(algebraMap Universal.Ring Field).comp (AdjoinRoot.mk _)` (Universal.lean:108).

In plain terms: this is the **functoriality of the `a₄`-coefficient under base change**, *specialised*
to this construction's algebra map and *re-spelled* so the image lands as `polyToField (CC curve.a₄)`
(the normal form the rest of the project's division-polynomial machinery is written against), rather
than as the raw `algebraMap R₀ Universal.Field curve.a₄`.

Variables / typeclasses involved (Lean side):
- none free — everything (`curve`, `pointedCurve`, `polyToField`, `Universal.Field`) is a fixed
  project constant. The lemma is fully concrete.

Hypotheses (Lean side):
- none.

Conclusion (math): `a₄(curve ⊗_{R₀} Universal.Field) = ι(a₄(curve))` for the structure map `ι = polyToField ∘ CC`.

Conclusion (Lean): `pointedCurve.a₄ = polyToField (CC curve.a₄)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `:= rfl` glue lemma — a definitional bridge re-spelling one coefficient of a base-changed
curve. Not a new structure, not a `## Main results` entry, not named after a person/place.

### One-line check (Phase 2b)

Body line count: 1 (`:= rfl`).
One-liner verdict: **n/a — kind is `lemma`, not `def`** (the def-specific one-liner gate does not
apply to propositions). Recorded for completeness: this is a one-line *proof* of a coefficient
identity, the strongest possible signal that it is a `simp`-normal-form bridge rather than content.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                       | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "base change Weierstrass curve coefficients a4 algebra map functoriality"                    | yes  | $`a_i(W\otimes_R A) = f(a_i(W))`$ under `f : R → A`     | Stanford 248B notes, arXiv 2302.10640 (Lean group-law paper), Magma/PARI handbooks. Standard, never named. |
|  2 | WebSearch (general form)         | "universal elliptic curve coordinate ring division polynomial coefficient base change"      | yes  | $`a'_i = u^i a_i`$ (coord change); $`a_i \in \mathbb{Z}[a_1..a_6,x,y]`$ | jtnb.881, arXiv 1303.5002, Sage `ell_generic`. The base-change-of-coefficient fact is folklore. |
|  3 | WebSearch (named-after/aliases)  | (covered by #1/#2 — concept has no eponym; "functoriality of Weierstrass coefficients")      | yes  | same as #1                                            | No named theorem; it is a one-line remark in every reference. |
|  4 | ChatGPT MCP                      | n/a — MCP down this session (task note). Compensated by extra WebSearch (#1–#3) + mathlib source read. | n/a  | —                                                     | Fallback per task instructions. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` (and `refs/`)                        | n/a  | dir not populated for this decl                       | recorded n/a. |
|  6 | nLab                             | "Weierstrass curve" / base change of coefficients                                           | n/a  | nLab has elliptic-curve-as-functor, not this coeff identity | too trivial / spelling-level for nLab. |
|  7 | nCatLab (if categorical)         | —                                                                                           | n/a  | not a categorical concept                             | the only "functoriality" here is the trivial `map_aᵢ`. |
|  8 | Stacks Project (if alg geom)     | Weierstrass equation base change                                                            | n/a  | Stacks treats Weierstrass models abstractly; no `aᵢ` re-spelling lemma | n/a — spelling-level. |
|  9 | MathOverflow / MSE              | "coefficients of base-changed Weierstrass equation"                                         | yes  | confirms folklore: $`a_i`$ map by the ring hom         | nothing beyond #1. |
| 10 | recent arXiv (last 5 years)      | division polynomial coefficients / EDS (1303.5002, 2102.07573, 2302.10640)                   | yes  | division polys live in `ℤ[a₁..a₆,x,y]`; coeffs base-change trivially | the *universal* `ℤ[aᵢ]` setup is exactly mathlib's `Universal` namespace + this project's fork. |

### Literature summary (Phase 3)

Concept identified as: **functoriality of a Weierstrass coefficient under a ring homomorphism / base
change** (here `aᵢ ↦ f(aᵢ)`), specialised to the universal curve's structure map.
Sources agree on the standard form: **yes** — universally treated as a one-line remark
(`aᵢ(W.map f) = f(aᵢ(W))`); no source elevates it to a named lemma.
Most general standard form: for any `f : R →+* A`, `(W.map f).aᵢ = f (W.aᵢ)` — i.e. mathlib's
`WeierstrassCurve.map_a₄`. Base change is the instance `f = algebraMap R A`.
Generality dimensions where the literature varies:
  - source ring: arbitrary commutative ring (most general) — the project pins `R₀ = ℤ[A₁..A₆]`.
  - target: arbitrary `f`-algebra — the project pins `Universal.Field`.
  - the *spelling* of the image (`f(aᵢ)` vs `polyToField (CC aᵢ)`) is a project-local convention,
    not a literature distinction.
Disagreement with the literature: **none mathematically.** The literature form is strictly more
general; the project lemma is a fixed-instance, re-spelled corollary.

---

### Generality analysis — `pointedCurve_a₄`

Literature-standard form (from Phase 3): `(W.map f).a₄ = f W.a₄` for arbitrary `W`, `f`.

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | the curve                    | fixed `Universal.curve` over `ℤ[A₁..A₆]`  | arbitrary `W : WeierstrassCurve R` | yes (trivially)     | the general statement is exactly mathlib `map_a₄`; nothing about `curve` is used. |
| 2 | the ring map                 | fixed `algebraMap _ Universal.Field` (via `baseChange`) | arbitrary `f : R →+* A`         | yes (trivially)     | mathlib's `map_a₄` already takes an arbitrary `f`. |
| 3 | the image spelling           | `polyToField (CC ·)`                      | `f (·)`                          | n/a (project glue)  | `polyToField ∘ CC = algebraMap R₀ Field` here; the re-spelling is project-local normalisation, not generality. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (a fixed-instance, re-spelled corollary of
mathlib's already-present `map_a₄`).
Number of weakening opportunities found: 2 (generalise the curve; generalise the ring map) — but
weakening it *is* mathlib's existing `map_a₄`, so there is nothing new to add.
Proposed restatement: the maximally general form already exists in mathlib as `WeierstrassCurve.map_a₄`.
Cost of restatement: n/a — no restatement to contribute (mathlib has the general form).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance?                                                  | no       | — | already a plain coefficient equation. |
|  2 | sequences/metric → filters/topology?                                                   | no       | — | no analytic content. |
|  3 | construct an object → universal-property class?                                        | no       | — | `map`/`baseChange` already exist in mathlib. |
|  4 | set-with-closure → bundled substructure?                                               | no       | — | n/a. |
|  5 | vector-space/field-specific → weaken typeclasses?                                      | no       | — | mathlib's `map_a₄` is already over arbitrary `CommRing` + ring hom. |
|  6 | 1-categorical → higher-categorical?                                                    | no       | — | n/a. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary algebra?                                            | no/already | — | the general form (`map_a₄`) is already index-free; the project merely *specialised* it. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** This is a concrete coefficient identity; the contemporary mathlib
idiom for it is precisely `@[simps] def map` producing `map_a₄`, which already exists. The only
"reformulation" is the project's spelling normalisation, which is not a mathlib generalisation.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `lemma`** (a proposition; introduces no definitional equality or
typeclass-search path). Skipped.

---

### Mathlib search-status: `pointedCurve_a₄`

[A] Lean-Finder       (index unavailable this session; compensated by [B]/[C]/[D])  n/a: tool offline
[B] Loogle            `(WeierstrassCurve.map _ _).a₄ = _ _`, `?W.a₄`                  hit: `WeierstrassCurve.map_a₄`
[C] LeanSearch        "coefficient a4 of base-changed / mapped Weierstrass curve"     hit: `map_a₄` (via `@[simps]` on `map`)
[D] Grep mathlib src  `map_a₄`, `@[simps] def map`, `baseChange`, `coe_algebraMap_eq_CC`, `pointedCurve`, `polyToField` hit (for `map_a₄`, `baseChange`, `coe_algebraMap_eq_CC`); NO hit for `pointedCurve`/`polyToField`
[E] Name pattern      grep repo+mathlib for `pointedCurve_a`, `polyToField`, `Universal.curve`  hit only in this project + HasseWeil fork; absent from mathlib

Searched for both:
  - the user's current form (`pointedCurve.a₄ = polyToField (CC curve.a₄)`) — **not in mathlib**
    (the names `pointedCurve`, `polyToField`, `Universal.curve` are project-only).
  - the literature-standard / general form (`(W.map f).a₄ = f W.a₄`) — **in mathlib** as
    `WeierstrassCurve.map_a₄`, `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230-232`
    (auto-generated by `@[simps]` on `def map`; it is itself `@[simp]`). `baseChange = map (algebraMap …)`
    (same file, line 236). Bivariate `coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC`
    (`Mathlib/Algebra/Polynomial/Bivariate.lean:148`).

Concluded: **found the GENERAL form in mathlib as `WeierstrassCurve.map_a₄`** (and `map_a₄`'s
`@[simps]` siblings `map_a₁/a₂/a₃/a₆`). The project lemma is a fixed-instance specialisation,
re-spelled through `polyToField ∘ CC`. The *specific spelling* is not in mathlib (it cannot be —
it mentions project-only constants), but every mathematical ingredient is.

---

### Call sites — `pointedCurve_a₄`

Internal use count (NagellLutz, excluding declaring file Universal.lean:163): **1**
  - `projects/NagellLutz/LutzNagell/ZSMul.lean:248` — `simp only [smulX_one, smulY_one, pointedCurve_a₁,
    pointedCurve_a₂, pointedCurve_a₄, …]` (used as a simp-normal-form rewrite, alongside the sibling
    `pointedCurve_aᵢ` lemmas).
External-to-project (forked copy, HasseWeil): the decl is **duplicated** at
`HasseWeil/Auxiliary/Universal.lean:166`, used at `HasseWeil/Auxiliary/DivisionPolynomial.lean:321`
(same simp pattern).

| Caller file:line                                              | Usage pattern (one-line excerpt)                                            |
|--------------------------------------------------------------|------------------------------------------------------------------------------|
| NagellLutz/LutzNagell/ZSMul.lean:248                          | `simp only [smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄, …]` |
| HasseWeil/Auxiliary/DivisionPolynomial.lean:321 (fork copy)  | `simp only [smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄, …]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `pointedCurve_a₄`?):
  - (none found) — but note `a₄` is used **less** than `a₁/a₂/a₃` in the simp sets; only one
    NagellLutz site references it (cf. `pointedCurve_a₁` at 4+ sites). The five `pointedCurve_aᵢ`
    lemmas are shipped as a *block*: this is the rarely-fired member of a normal-form family.

What the pattern tells you: K=1 internal use, always inside a `simp only` together with the sibling
`pointedCurve_aᵢ` lemmas, to push `pointedCurve.a₄` into the `polyToField (CC ·)` normal form. This
is a `simp`-normalisation bridge, not standalone API — exactly the profile of a NO-composable
spelling lemma. The fork duplication reinforces that it is project scaffolding, not a mathlib
contribution.

---

### Composition check (Phase 6)

Can `pointedCurve_a₄` be derived from mathlib in ≤3 chained calls?

Attempt 1: unfold `baseChange` → `map`, apply mathlib `map_a₄`, then close the spelling with the
project's own `rfl`-lemma `algebraMap_field_eq_comp`:
```lean
example : pointedCurve.a₄ = polyToField (CC curve.a₄) := by
  rw [show pointedCurve.a₄ = algebraMap _ Universal.Field curve.a₄ from
        WeierstrassCurve.map_a₄ ..,            -- mathlib: (curve.map f).a₄ = f curve.a₄
      algebraMap_field_eq_comp]                -- project rfl-lemma (Universal.lean:113):
                                               --   algebraMap R₀ Field = polyToField.comp (algebraMap R₀ Poly)
  rfl                                          -- algebraMap R₀ Poly curve.a₄ = CC curve.a₄  (Bivariate coe_algebraMap_eq_CC)
```
  - Mathlib decls used: `WeierstrassCurve.map_a₄`, `Polynomial.coe_algebraMap_eq_CC` (the final `rfl`).
  - Result: **succeeds** — in fact the whole lemma is already closed by `rfl` (as in source), because
    `baseChange`/`map`/`algebraMap`/`polyToField`/`CC` are all definitional. The `map_a₄` route is
    the explicit-step version of the same chain.
  - Notes: ≤3 mathlib-anchored steps (one of which is the project's own `:= rfl` bridge
    `algebraMap_field_eq_comp`). No new mathematical idea.

Conclusion: **COMPOSABLE.** It is `rfl`/`simp [map_a₄, algebraMap_field_eq_comp]` — a definitional
bridge between mathlib's `map_a₄` and this project's `polyToField ∘ CC` spelling.

---

## Verdict: `WeierstrassCurve.Universal.pointedCurve_a₄`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the only content is the folklore "coefficients base-change by the ring
  hom" — never a named result; the general form is mathlib's `map_a₄`.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a fixed-instance, re-spelled
  corollary; the general form already lives in mathlib.
- Mathlib search (Phase 5): general form found as `WeierstrassCurve.map_a₄` (Weierstrass.lean:230-232,
  `@[simp]` via `@[simps]`); the project's exact spelling mentions project-only constants
  (`pointedCurve`, `polyToField`) and is therefore necessarily absent from mathlib.
- Composition check (Phase 6): COMPOSABLE — `rfl`, equivalently `map_a₄` + the project's `:= rfl`
  bridge `algebraMap_field_eq_comp` (+ Bivariate `coe_algebraMap_eq_CC`).

**Rationale:**

`pointedCurve_a₄` is a project-local `simp`-normal-form bridge, not new mathematics. Mathlib already
proves the general statement `(W.map f).a₄ = f W.a₄` as the `@[simp]` lemma
`WeierstrassCurve.map_a₄` (auto-generated by `@[simps]` on `def map`), and `baseChange` is *defined*
as `map (algebraMap …)`. The project lemma merely instantiates this at the universal curve and the
universal field, and re-spells the image `algebraMap R₀ Universal.Field curve.a₄` as
`polyToField (CC curve.a₄)` — the normal form the division-polynomial / ZSMul proofs are written
against. Because that spelling names project-only constants (`polyToField`, `CC ∘ …` for *this*
algebra map), the exact lemma can never go to mathlib; and because it is literally `rfl`, it needs
no lemma at all — it is a ≤3-step composition (`map_a₄` + the project's own `rfl`-bridge
`algebraMap_field_eq_comp`).

It is **correct and useful as a local `simp` lemma** — keeping the five `pointedCurve_aᵢ` family for
ergonomic rewriting inside this project is entirely reasonable, and this report does *not* recommend
deleting it from the project. The verdict is strictly about mathlib inclusion: mathlib should not (and
structurally cannot) take this re-spelled, fixed-instance form. The thing mathlib *does* want — the
general coefficient functoriality — it already has.

**WHY not (refactor-actionable):**
- Mathlib has the building block: `WeierstrassCurve.map_a₄`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230-232`), plus `baseChange = map (algebraMap …)`
  (same file:236) and `Polynomial.coe_algebraMap_eq_CC` (`Mathlib/Algebra/Polynomial/Bivariate.lean:148`).
  The project lemma is the 1–3-call composition of these with the project's own `:= rfl` bridge
  `algebraMap_field_eq_comp` (Universal.lean:113).

Mathlib building blocks: `WeierstrassCurve.map_a₄`, `WeierstrassCurve.baseChange` (def),
`Polynomial.coe_algebraMap_eq_CC`; plus project `:= rfl` lemma `algebraMap_field_eq_comp`.
Composition sketch (≤3 lines):
```lean
example : pointedCurve.a₄ = polyToField (CC curve.a₄) := by
  rw [WeierstrassCurve.map_a₄, algebraMap_field_eq_comp]; rfl
-- (or simply `:= rfl`, exactly as in source — everything is definitional)
```
Call sites in our project (from Phase 6.0): **1** in NagellLutz (ZSMul.lean:248), 1 in the HasseWeil fork.

Refactor plan (mathlib-inclusion view only — NOT a recommendation to delete the local lemma):
this lemma is *not a mathlib candidate*. If one nonetheless wanted to remove it, at the single
NagellLutz call site (ZSMul.lean:248, inside a `simp only [...]`) one would replace `pointedCurve_a₄`
with `[WeierstrassCurve.map_a₄, algebraMap_field_eq_comp, Polynomial.coe_algebraMap_eq_CC]` (and
correspondingly for its `a₁/a₂/a₃/a₆` siblings). Given the lemma is `rfl` and the family is used as a
unit, keeping the local `pointedCurve_aᵢ` block is the pragmatic choice; the actionable mathlib outcome
is simply **do not upstream it**. The genuinely-upstreamable neighbour, if any, would be the *def*
`polyToField` / the `Universal` construction itself — assessed separately (see
`.mathlib-quality/overview/mathlibable/polyToField.md`, `pointedCurve.md`, `curve.md`).

Next action: do **not** add `pointedCurve_a₄` to mathlib. Mathlib already has the general
`map_a₄`. Keep the lemma as project-local `simp` glue (its current, correct role); no mathlib PR.
If the broader `Universal` curve construction is upstreamed later, these `pointedCurve_aᵢ` simp
lemmas travel with it as `@[simps]`-style accessors, not as standalone contributions.

---

## Next step

Do not add to mathlib. The general form is already present as `WeierstrassCurve.map_a₄`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230-232`); the project lemma is a `rfl`
specialisation re-spelled through `polyToField ∘ CC`, composable in ≤3 calls. Retain it as local
`simp` glue for the division-polynomial / ZSMul development.
