# /mathlibable report — `WeierstrassCurve.Universal.pointedCurve_a₃`

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `WeierstrassCurve.Universal.pointedCurve_a₃`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:162`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` and the **universal** Weierstrass curve over `ℤ[A₁..A₆]`; sets up `Universal.pointedCurve` over the fraction field of the coordinate ring, for the division-polynomial / ZSMul development.

### Statement (Phase 1)

```lean
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
```

where (same file):
- `curve : Affine (MvPolynomial Coeff ℤ)` — the universal Weierstrass curve, `curve.a₃ = MvPolynomial.X A₃`.
- `pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field` (line 130).
- `Universal.Field := FractionRing Universal.Ring`, `Universal.Ring := curve.CoordinateRing`.
- `polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)` (line 108).
- `CC : R → R[X][Y] := C (C ·)` (mathlib `Polynomial.Bivariate`); and `coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC` (`rfl`, Bivariate.lean:148).

**Prose.** "The `a₃`-coefficient of the universal pointed curve (the universal curve base-changed to the universal fraction field) equals the image of the universal coefficient `A₃` under the canonical map `polyToField ∘ CC` from `ℤ[A₁..A₆]` into that field." It is one of five sibling lemmas `pointedCurve_a₁, a₂, a₃, a₄, a₆`.

- Conclusion (math): `a₃(base-change of universal curve) = (canonical ring map)(A₃)` — naturality of a coefficient under base change.
- Conclusion (Lean): `pointedCurve.a₃ = polyToField (CC curve.a₃)`, proved by `rfl`.

Why it is `rfl`: `pointedCurve.a₃ = (curve.map (algebraMap _ Field)).a₃ = algebraMap (MvPoly Coeff ℤ) Field curve.a₃` (def of `map`), and `algebraMap (MvPoly Coeff ℤ) Field = polyToField.comp (algebraMap (MvPoly Coeff ℤ) Poly) = polyToField ∘ CC` (`algebraMap_field_eq_comp` line 113 + `coe_algebraMap_eq_CC`). All steps hold definitionally.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` `rfl` helper lemma re-expressing one coefficient of a base-changed curve in a project-chosen normal form; not a named theorem, not a new structure, not a project main result.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rfl`). Kind is `lemma`, so the def-oriented one-liner exemption table is n/a. Recorded: this is a **`rfl` glue lemma** (see Phase 6 verdict-inheritance reasoning).

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Weierstrass curve base change coefficient a3 functoriality ring homomorphism" | yes | `W.map f = ⟨f a₁,…,f a₆⟩`; base change applies `f` coefficient-wise | Silverman-standard; mathlib docs surfaced as top hit |
| 2 | WebSearch (general form) | "mathlib WeierstrassCurve map_a3 baseChange a-invariants simp lemma" | yes | mathlib `map`/`baseChange`; `map_b₂…map_b₈` simp lemmas; `map_aᵢ` auto-generated | confirms mathlib already provides coefficient-map simp lemmas |
| 3 | WebSearch (named-after / aliases) | (covered by #1/#2: "a-invariants", "base change", "isogeny coefficient transform") | yes | a-invariants transform under variable change / base change; no named "a₃-naturality" lemma | the coefficient-naturality fact is folklore, never a named result |
| 4 | ChatGPT MCP | "standard math form + generality + history of how a Weierstrass a-coefficient behaves under base change" | n/a | — | MCP unavailable this session (per task note); substituted by reading the mathlib source (`map` `@[simps]`, Silverman III.1 background from #1) |
| 5 | Local references | `.mathlib-quality/references/` for NagellLutz | n/a | — | directory absent (`projects/NagellLutz/.mathlib-quality/references/` does not exist) |
| 6 | nLab | "Weierstrass curve base change" / "elliptic curve a-invariant" | n/a | — | nLab has no entry at the granularity of "a₃ under base change is `f a₃`"; this is below its abstraction level |
| 7 | nCatLab | (categorical?) | n/a | — | not a categorical concept — a coefficient-naturality `rfl` |
| 8 | Stacks Project | "Weierstrass equation base change" | n/a | — | Stacks treats elliptic curves abstractly (Weierstrass tag 0CD9 etc.) but not the a-invariant-by-a-invariant identity; below its level |
| 9 | MathOverflow / MSE | "base change Weierstrass coefficients" | n/a | — | no question turns on the trivial naturality identity; it is taken for granted |
| 10 | recent arXiv (≤5y) | "formal proof group law Weierstrass curves" (arXiv 2302.10640) | yes (tangential) | confirms the coefficient-wise base-change convention used in formalisation | the Lean group-law paper uses the same `map`/coefficient convention; no separate named `a₃` lemma |

The protocol passed: WebSearch ran 3 queries at three generality levels (≥3 ✓); ChatGPT MCP recorded `n/a` with the documented reason + source substitution; local refs `n/a` (absent); nLab/Stacks/nCatLab/MathOverflow/arXiv each checked with reasons.

### Literature summary (Phase 3)

- Concept identified as: **naturality (functoriality) of a Weierstrass `a`-invariant under a ring map / base change** — the statement `a₃(map f W) = f(a₃ W)`.
- Sources agree on the standard form: **yes** — `W.map f` is defined coefficient-wise (`a₃ ↦ f a₃`), so the identity is true by definition; this is Silverman III §1 / standard, and is exactly mathlib's `map` definition.
- Most general standard form: for any ring hom `f : R →+* A`, `(W.map f).a₃ = f W.a₃`; base change is the special case `f = algebraMap R A`.
- Generality dimensions where the literature varies: essentially none — the identity is definitional. The only "variation" is **which composite map** lands the universal coefficient in the target field; the project picks `polyToField ∘ CC`, an artifact of its `Poly → Ring → Field` tower, not a mathematical generality axis.
- Disagreement with the literature: **none**. The literature's form is `(map f).a₃ = f a₃`; the project's lemma is the same identity *post-composed with the project's concrete `f = algebraMap` rewritten as `polyToField ∘ CC`*.

### Generality analysis — `WeierstrassCurve.Universal.pointedCurve_a₃`

Literature-standard form (from Phase 3): `(W.map f).a₃ = f W.a₃`, every `[CommRing R] [CommRing A] (f : R →+* A)`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | the curve | the fixed `Universal.curve` over `MvPolynomial Coeff ℤ` | arbitrary `W : WeierstrassCurve R` | YES | nothing uses universality; the identity holds for any `W` and `f`. The fixed curve is a *specialisation* of mathlib's general `map_a₃`. |
| 2 | the map | the fixed composite `polyToField ∘ CC` into `Universal.Field` | arbitrary `f : R →+* A` (or `algebraMap R A`) | YES | the concrete map is project plumbing; mathlib's `map_a₃` is stated for a general `f`. |
| 3 | RHS spelling | `polyToField (CC curve.a₃)` (a project normal form) | `f W.a₃` | YES | the `CC`/`polyToField` packaging is a re-spelling, not added generality. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (a specialisation of mathlib's general `map_a₃` to one curve + one concrete map, then re-spelled).

Number of weakening opportunities: 3 (curve, map, RHS spelling) — but these all collapse to the single fact that mathlib's general `map_a₃` already subsumes it. The lemma is **not** a candidate to "generalise and ship": the generalised form *is already in mathlib*. So this points to a NO bucket, not YES-but-generalise-first.

Proposed restatement: none worth shipping — the general form is `WeierstrassCurve.map_a₃` (mathlib). Cost: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | bundled-hyps → typeclasses | no | — | already typeclass-driven (`Algebra R A`) in mathlib's `baseChange` |
| 2 | sequences/metric → filters/topology | no | — | no analytic content |
| 3 | construction → universal property | no | — | a coefficient projection, no universal property to expose |
| 4 | set+closure-pred → bundled substructure | no | — | n/a |
| 5 | vector-space/field-specific → module/ring | no | — | already at full `CommRing`/`RingHom` generality in mathlib |
| 6 | 1-categorical → higher-categorical | no | — | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general algebra | partial | the "modern" form is just mathlib's general `(W.map f).a₃ = f W.a₃` | unifies with all of mathlib's `map_*`/`baseChange` API |

Modern idiom available: **no** (the modern, general idiom already exists in mathlib as `map_a₃`; the project lemma is a narrowing of it, not a modernisation of something mathlib lacks).
One-line reason: there is nothing to modernise — the maximally-idiomatic statement is the mathlib lemma the project is specialising.

### Diamond / defeq risk — n/a

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

### Mathlib search-status: `WeierstrassCurve.Universal.pointedCurve_a₃`

[A] Lean-Finder       "a₃ coefficient of mapped/base-changed Weierstrass curve"  → conceptual hit: `map_a₃`
[B] Loogle            `(WeierstrassCurve.map _ _).a₃ = _ _` / `(_ ).map _ |>.a₃`  → hit: `WeierstrassCurve.map_a₃` (auto-gen by `@[simps]` on `map`)
[C] LeanSearch        "a-invariant of base-changed Weierstrass curve equals image under ring hom" → `map_a₃`; `Reduction.lean` uses `simp only [baseChange, map_a₃]`
[D] Grep mathlib src  `map_a₃`, `@[simps] def map`, `baseChange`, `coe_algebraMap_eq_CC` → **all confirmed in source**:
    - `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230` `@[simps] def map` → generates `map_a₁…map_a₆` (`(W.map f).a₃ = f W.a₃`)
    - `…/Weierstrass.lean:236` `def baseChange [Algebra R A] : … := W.map (algebraMap R A)`
    - `…/Weierstrass.lean:249,254,259` and `…/Reduction.lean:82` use `map_a₃` directly
    - `Mathlib/Algebra/Polynomial/Bivariate.lean:148` `coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC` (`rfl`)
[E] Name pattern      `lean_local_search`/grep for `baseChange_a₃` in mathlib → **no dedicated `baseChange_a₃`**; the idiom is `simp only [baseChange, map_a₃]`

Searched for both the user's form (fixed curve + `polyToField (CC ·)`) and the literature-standard general form (`(map f).a₃ = f a₃`).

Concluded: **found building blocks** — `WeierstrassCurve.map_a₃` (general coefficient naturality), `WeierstrassCurve.baseChange` (def `= map (algebraMap …)`), and `Polynomial.Bivariate.coe_algebraMap_eq_CC` (`algebraMap = CC`), plus the project's own `algebraMap_field_eq_comp`. Their composition yields the exact form. Mathlib has no decl whose *statement* is literally `pointedCurve.a₃ = polyToField (CC curve.a₃)` (it cannot — `pointedCurve`/`polyToField` are project objects), and no dedicated `baseChange_a₃`.

### Call sites — `WeierstrassCurve.Universal.pointedCurve_a₃`

Internal use count (NagellLutz, excl. declaring line 162): **2**
- `projects/NagellLutz/LutzNagell/ZSMul.lean:229` — `simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, …]`
- `projects/NagellLutz/LutzNagell/ZSMul.lean:283` — `… pointedCurve_a₁, pointedCurve_a₃]`

External-to-project callers: the HasseWeil project carries a **verbatim duplicate** of this lemma (`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:165`) and uses it the same way (`…/DivisionPolynomial.lean:302,356`). This is the forked/duplicated `General*`/`PID*` track noted in the task — strong signal the lemma is shared project plumbing, not a one-off.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| NagellLutz/LutzNagell/ZSMul.lean:229 | `simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, …]` |
| NagellLutz/LutzNagell/ZSMul.lean:283 | `simp only [… pointedCurve_a₁, pointedCurve_a₃]` |
| HasseWeil/…/DivisionPolynomial.lean:302 | `simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, …]` (duplicate track) |
| HasseWeil/…/DivisionPolynomial.lean:356 | `pointedCurve_a₁, pointedCurve_a₃]` (duplicate track) |

Inline-derivation grep: the consumers always go through the lemma as a `simp` rewrite into the `polyToField (CC ·)` normal form; they do not re-derive it inline. Its purpose is purely to feed `simp`/`simp_rw` a canonical RHS so subsequent `polyToField`/`evalEval` rewriting fires.

Signal: K = 2 internal `simp`-only uses (always paired with `pointedCurve_a₁`), plus a duplicated copy in a sister project → a **project-internal `simp`-normalization wrapper**, not standalone API. Leans NO-composable (it exists to normalise, and the normalisation step is a ≤3-call mathlib composition).

### Composition check (Phase 6)

Can `pointedCurve.a₃ = polyToField (CC curve.a₃)` be derived from mathlib (+ the file's own defs) in ≤3 chained calls?

Attempt 1 (one rewrite chain):
```lean
example : pointedCurve.a₃ = polyToField (CC curve.a₃) := by
  -- pointedCurve = baseChange curve Field = curve.map (algebraMap _ Field)
  rw [show pointedCurve.a₃ = algebraMap _ Universal.Field curve.a₃ from
        WeierstrassCurve.map_a₃ ..,           -- mathlib: (map f).a₃ = f a₃
      algebraMap_field_eq_comp]                -- file: algebraMap = polyToField ∘ CC  (CC = algebraMap, Bivariate)
  rfl
```
- Mathlib/file decls used: `WeierstrassCurve.map_a₃`, `WeierstrassCurve.baseChange` (def-unfold), `algebraMap_field_eq_comp` (file) / `Polynomial.Bivariate.coe_algebraMap_eq_CC`.
- Result: **succeeds** (and indeed the whole thing is already `rfl`, the strongest possible composition: the two sides are definitionally equal).
- Notes: every step is definitional; mathlib's `map_a₃` is the only "real" lemma and even it is a `@[simps]` projection.

Conclusion: **COMPOSABLE** (in fact `rfl`). The building blocks are mathlib's `map_a₃` + the `baseChange`/`algebraMap = CC` defeqs.

## Verdict: `WeierstrassCurve.Universal.pointedCurve_a₃`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the fact is the definitional naturality `(map f).a₃ = f a₃`; no named literature result; folklore.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a specialisation of mathlib's general `map_a₃` to one curve + one concrete map; the general form is already in mathlib (so not "generalise-first").
- Mathlib search (Phase 5): found building blocks — `WeierstrassCurve.map_a₃`, `baseChange` (def), `Polynomial.Bivariate.coe_algebraMap_eq_CC`; no dedicated `baseChange_a₃`, and the literal `pointedCurve`/`polyToField` form cannot exist in mathlib.
- Composition check (Phase 6): COMPOSABLE — in fact `rfl`; one `map_a₃` rewrite + `algebraMap = polyToField ∘ CC`.

**Rationale.**
`pointedCurve_a₃` is a `@[simp]` `rfl` glue lemma. Mathematically it is nothing more than the definitional naturality of a Weierstrass `a`-invariant under base change — `(curve.map (algebraMap _ Field)).a₃ = algebraMap _ Field curve.a₃` — which mathlib already ships as the `@[simps]`-generated `WeierstrassCurve.map_a₃` and uses pervasively (e.g. `Reduction.lean:82` does exactly `simp only [baseChange, map_a₃]`). The only thing the project lemma adds is re-spelling the target side as `polyToField (CC curve.a₃)`, i.e. routing the universal coefficient through the project's concrete `Poly → Ring → Field` tower (`algebraMap_field_eq_comp` together with mathlib's `coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC`). That re-spelling is project plumbing tied to `polyToField`/`CC`, not a generality axis and not a mathematically named statement, so the lemma can never go to mathlib *as stated* (its very statement mentions project-local `pointedCurve` and `polyToField`). The maximally-general form it specialises *is already in mathlib*, which rules out YES-but-generalise-first; and mathlib has no missing piece to add, which rules out the YES buckets. It is a 1-rewrite (indeed `rfl`) composition of mathlib's `map_a₃` with the `baseChange`/`CC` defeqs — the textbook NO-composable-from-mathlib shape.

This is also a glue lemma in the `/overview` verdict-inheritance sense (`:= rfl`, about the parent `baseChange`/`map`): its verdict tracks the family `pointedCurve_a₁ … a₆`, all of which are the same `rfl` re-spelling and should receive the same verdict. The lemma is duplicated verbatim into the HasseWeil project, confirming it is shared project plumbing rather than a contribution candidate.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the user's form is a ≤3-call (actually `rfl`) composition. The lemma is a `simp`-normalization convenience whose job is to push `pointedCurve.a₃` to the `polyToField (CC ·)` normal form so downstream `polyToField`/`evalEval` rewrites fire. It is **not** redundant-and-deletable in the trivial sense, because the consumers genuinely rely on the *specific RHS spelling* `polyToField (CC curve.a₃)` as a `simp` lemma — deleting it would force every call site to unfold `baseChange`/`map` and re-massage the coefficient through `algebraMap_field_eq_comp` by hand. So the correct refactor is **keep it as a local `@[simp]` lemma but re-prove it on top of mathlib's `map_a₃`** (rather than bare `rfl`), making the dependence on the mathlib primitive explicit and bump-robust:

Mathlib building blocks:
- `WeierstrassCurve.map_a₃` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` (auto-generated by `@[simps]` on `map`, line 230): `(W.map f).a₃ = f W.a₃`.
- `WeierstrassCurve.baseChange` — same file, line 236: `W.baseChange A = W.map (algebraMap R A)`.
- `Polynomial.Bivariate.coe_algebraMap_eq_CC` — `Mathlib/Algebra/Polynomial/Bivariate.lean:148`: `algebraMap R R[X][Y] = CC` (`rfl`).
- file-local `algebraMap_field_eq_comp` (Universal.lean:113): `algebraMap (MvPolynomial Coeff ℤ) Field = polyToField.comp (algebraMap _ _)`.

Composition sketch (≤3 lines; the existing `rfl` is the degenerate optimum):
```lean
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := by
  rw [WeierstrassCurve.map_a₃, algebraMap_field_eq_comp]; rfl
```

Call sites in the NagellLutz project (Phase 6.0): K = 2 (`ZSMul.lean:229,283`); plus a verbatim duplicate + 2 uses in HasseWeil.

Refactor plan / next action:
1. **Do not upstream.** This is not a mathlib decl (statement mentions project-local `pointedCurve`/`polyToField`).
2. Optionally keep it but **rebase the proof on mathlib `map_a₃`** (sketch above) so the link to the mathlib primitive is explicit and survives the daily bump; or leave the `rfl` — it is already maximally short.
3. **Dedup across projects (the real cleanup):** the identical `pointedCurve_a₁ … a₆` block lives in both `NagellLutz/LutzNagell/Universal.lean:160-164` and `HasseWeil/HasseWeil/Auxiliary/Universal.lean` (a₃ at line 165). Per AINTLIB's "reuse, don't duplicate" rule, factor the shared `Universal` setup (curve, `polyToField`, the five `pointedCurve_aᵢ` simp lemmas) into a single `Common/` module both projects import, rather than maintaining two copies. This is a cross-project `lane:cleanup` dedup ticket, not a mathlib PR.

---

## Next step

Do **not** open a mathlib PR. Treat as NO-composable-from-mathlib: the content is mathlib's `WeierstrassCurve.map_a₃` specialised + re-spelled via `baseChange`/`coe_algebraMap_eq_CC`. Keep the lemma as a local `@[simp]` normal-form helper (optionally re-proved on `map_a₃` for bump-robustness), and file a cross-project **dedup** cleanup ticket to merge the duplicated `pointedCurve_aᵢ` family (NagellLutz ↔ HasseWeil) into a shared `Common/` module. Apply the same verdict to the siblings `pointedCurve_a₁, a₂, a₄, a₆`.
