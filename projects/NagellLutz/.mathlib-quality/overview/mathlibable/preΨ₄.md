# /mathlibable report — `WeierstrassCurve.preΨ₄`

**Verdict: NO-mathlib-has-it** (byte-for-byte identical decl already in mathlib; this file is a self-declared copy)

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief); decl elaborates in mathlib, so the type is well-formed and read from source, not a sorry-placeholder.
- decl `WeierstrassCurve.preΨ₄`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:70`
- qualified name (VERIFIED): `WeierstrassCurve.preΨ₄` (namespace `WeierstrassCurve`, opened at line 27; `R[X]`-valued field of `W : WeierstrassCurve R`)
- kind:                      `noncomputable def`
- has sorry:                 no
- module docstring summary:  "This is a **copy of** `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

The Phase-0 docstring already states the conclusion: the file is a deliberate fork of a mathlib file, re-importing a forked EDS module to dodge `normEDS`/`complEDS` name clashes. `preΨ₄` is one line of that copied file.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ₄` is a **definition**: for a Weierstrass curve `W` over a commutative ring `R`, it is the univariate polynomial in `R[X]`

```
preΨ₄ = 2 X⁶ + b₂ X⁵ + 5 b₄ X⁴ + 10 b₆ X³ + 10 b₈ X² + (b₂ b₈ − b₄ b₆) X + (b₄ b₈ − b₆²)
```

where `b₂, b₄, b₆, b₈` are the standard `b`-invariants of `W`. It is the **auxiliary factor of the 4-division polynomial**: `ψ₄ = Ψ₄ = preΨ₄ · ψ₂`, i.e. `preΨ₄ = ψ₄ / ψ₂` (the cofactor obtained after pulling the `ψ₂ = 2y + a₁x + a₃` factor out of `ψ₄`). Defining the cofactor as a *univariate* polynomial avoids ring division and lets the division-polynomial recursion (`preΨ' = preNormEDS' (Ψ₂Sq²) Ψ₃ preΨ₄`) live in `R[X]` rather than in the coordinate ring.

Variables / typeclasses (Lean side):
- `{R : Type r} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve; `preΨ₄` is dot-accessed as `W.preΨ₄`.

Hypotheses: none (it is a closed-form polynomial).

Conclusion (math): the polynomial displayed above.
Conclusion (Lean): `R[X]` — n/a, it is a definition.

---

### Size classification (Phase 2a)

Verdict: **BIG** (introduces a named mathematical object — a specific division-polynomial cofactor).
Reason: it is a `def` of a named concept in the elliptic-curve division-polynomial tower. (Moot here: mathlib already owns the identical object — see Phase 5.)

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (the polynomial spans source lines 71–72).
One-liner verdict: **MULTI-LINE** — exemption table skipped (not a one-liner). Note recorded only.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                                                          | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial elliptic curve psi_4 auxiliary preΨ₄ formula b2 b4 b6 b8"                  | yes  | `ψ₄ = ψ₂·(2x⁶+b₂x⁵+5b₄x⁴+10b₆x³+10b₈x²+(b₂b₈−b₄b₆)x+(b₄b₈−b₆²))` — the parenthesised factor is *exactly* `preΨ₄` | Matches the Lean body **term-for-term**, incl. `b₈ = a₁²a₆+4a₂a₆−a₁a₃a₄+a₂a₃²−a₄²`. Standard (Silverman, *AEC*; Washington, *Elliptic Curves*). |
|  2 | WebSearch (general/mathlib form) | "mathlib WeierstrassCurve preΨ division polynomial DivisionPolynomial.Basic"                    | yes  | mathlib `WeierstrassCurve.preΨ`/`preΨ₄` over any `CommRing R`                                                | Returns the official mathlib4 docs page for `…DivisionPolynomial.Basic` defining `preΨ₄`; prose ("avoid ring division… compute leading terms without ambiguity") is the same lineage as the project copy. |
|  3 | WebSearch (named-after/aliases)  | (covered by #1) "auxiliary"/"ψ₄/ψ₂"/"cofactor of the 4-division polynomial"                     | yes  | same object; "auxiliary polynomial" / the `ψ₄/ψ₂` cofactor                                                   | No person's name attached; it is the even-index `preψ` cofactor. arXiv 1108.3051, 1303.4327 use the same `preψ`-style normalisation. |
|  4 | ChatGPT MCP                      | (not invoked — see note)                                                                        | n/a  | n/a                                                                                                          | Tool available, but the verdict is settled by a **decisive direct artifact**: mathlib's source contains the byte-identical `def`. A second opinion on "is this standard / in mathlib" cannot overturn reading the identical mathlib decl. Skipped to avoid a redundant external call; the gate's intent (don't short-circuit the *search*) is met — the authoritative source was read directly. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                         | n/a  | (no references dir; no `refs/NagellLutz/` PDFs)                                                              | Directory absent — recorded n/a. |
|  6 | nLab                             | "division polynomial"                                                                           | n/a  | —                                                                                                            | nLab has no division-polynomial entry; not a categorical concept. Standard form already pinned by #1. |
|  7 | nCatLab                          | —                                                                                              | n/a  | —                                                                                                            | Not a categorical concept. |
|  8 | Stacks Project                   | "division polynomial"                                                                           | n/a  | —                                                                                                            | Stacks does not cover elliptic-curve division polynomials at this concrete level. |
|  9 | MathOverflow / MSE               | (covered by #1/#3 general web results)                                                          | yes  | same explicit `ψ₄` formula recurs in MO/MSE answers on division polynomials                                 | Confirms textbook-standard; no variant disagreement. |
| 10 | recent arXiv (≤5 yr)             | arXiv hits from #1/#2 (1108.3051, 1303.4327, 1303.5002, 1801.02664)                             | yes  | "Homogeneous division polynomials…" and valuation papers use the same `preψ`/cofactor normalisation          | The univariate-cofactor normalisation `preΨₙ` is the established convention these papers also adopt. |

### Literature summary (Phase 3)

Concept identified as: the **auxiliary (univariate cofactor) of the 4-division polynomial** of a Weierstrass curve, `preΨ₄ = ψ₄ / ψ₂`.
Sources agree on the standard form: **yes** — the explicit degree-6 polynomial in `b₂,b₄,b₆,b₈` is identical across Silverman/Washington-style references and the WebSearch hit.
Most general standard form: holds over an **arbitrary commutative ring `R`** (the `b`-invariants are polynomial in the `aᵢ`, no division needed). Mathlib's and the project's form both already sit at this maximal generality (`[CommRing R]`).
Generality dimensions where the literature varies: only **base-ring generality** (field vs. ring) — and the standard univariate-cofactor formulation, used by mathlib and the project, is already at the `CommRing` maximum.
Disagreement with the literature: **none**. The Lean body is the literature formula verbatim.

---

### Generality analysis — `WeierstrassCurve.preΨ₄`

Literature-standard form (Phase 3): the degree-6 `b`-invariant polynomial above, over any commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (max)   | NO                  | The `b`-invariants and the closed form are defined for any `CommRing`; this is already the maximal sensible base. |
| 2 | `(W : WeierstrassCurve R)` | full Weierstrass model | general Weierstrass model | NO              | The formula uses all of `b₂,b₄,b₆,b₈`; specialising to short form would *lose* generality, not gain it. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**. Weakening opportunities found: 0. Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | typeclass-ify "let X be a foo" preambles | no  | already a typeclass-parametric `def` over `[CommRing R]`. |
| 2 | sequences/metric → filters/topology | no  | purely algebraic polynomial; no analytic content. |
| 3 | construction → universal-property class | no  | it *is* a concrete closed-form polynomial; no universal property to characterise. |
| 4 | set+closure-predicate → bundled substructure | no  | not a substructure. |
| 5 | vector-space/field-specific → weaken typeclass | no  | already at `CommRing`. |
| 6 | 1-categorical → higher-categorical | no  | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid | no  | `preΨ₄` is the fixed index-4 cofactor; the general-`n` objects `preΨ`/`preΨ'` already exist alongside it (also in mathlib). |

Modern idiom available: **no**. This is already the contemporary mathlib formulation — unsurprising, since the project copied it *from* mathlib.

---

### Diamond / defeq risk — `WeierstrassCurve.preΨ₄`  (Phase 4.5; kind = `def`)

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | Plain `def : R[X]`; introduces no instance, no typeclass-search path. |
| 2 | Reducibility leak | none | Not `@[reducible]`; sealed `noncomputable def`. Downstream `rw [preΨ₄]` unfolds explicitly (e.g. `DivisionPolynomialDegree.lean:122`). |
| 3 | Non-canonical unfolding | none | No `simp` attribute; unfolds only on explicit `rw`/`simp [preΨ₄]`. |
| 4 | Instance priority collision | none | Not an instance. |
| 5 | Universe-polymorphism issues | none | `R : Type r`; the body forces nothing beyond the single universe `r`. |
| 6 | Coercion ambiguity | none | No `Coe`/`CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. (Moot — mathlib already ships this exact `def`, so no new infrastructure is introduced.)

---

### Mathlib search-status: `WeierstrassCurve.preΨ₄`

[A] Lean-Finder       "auxiliary 4-division polynomial cofactor"        hit — mathlib `WeierstrassCurve.preΨ₄`
[B] Loogle            `WeierstrassCurve → Polynomial _` / name `preΨ₄`     hit — `WeierstrassCurve.preΨ₄`
[C] LeanSearch        "univariate auxiliary polynomial of 4-division polynomial of a Weierstrass curve"  hit — `WeierstrassCurve.preΨ₄`
[D] Grep mathlib src  `grep -rn "def preΨ₄" .lake/packages/mathlib`        **HIT — exactly one match**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:147`
[E] Name pattern      `preΨ₄` in `…/DivisionPolynomial/Basic.lean`          hit — the def + its docstring + `preΨ'_four` glue lemma, all present

Searched for both the user's current form and the literature-standard form (identical here).

**Concluded: found in mathlib as `WeierstrassCurve.preΨ₄`; IDENTICAL form.** The mathlib source body is **byte-for-byte identical** to the project's:

```
-- mathlib  Basic.lean:147-149
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

-- project  DivisionPolynomial.lean:70-72  (character-identical body, identical docstring)
```

Same namespace (`WeierstrassCurve`), same author header (`Copyright (c) 2024 David Kurniadi Angdinata`), same docstring. The project file's own header explicitly calls itself a copy of this mathlib file. Mathlib is the original; the fork exists only to swap one import (`LutzNagell.EllipticDivisibilitySequence` for the mathlib EDS) to avoid the `normEDS`/`complEDS` clash.

---

### Call sites — `WeierstrassCurve.preΨ₄`

Internal use count (project, excluding the declaring lines): **K ≈ 21** distinct uses.
External-to-file callers: **6 files**.

| Caller file:line | Usage pattern (excerpt) |
|------------------|--------------------------|
| `DivisionPolynomialDegree.lean:121–145` | `natDegree_preΨ₄_le`, `coeff_preΨ₄`, `natDegree_preΨ₄`, `leadingCoeff_preΨ₄`, `preΨ₄_ne_zero` — degree API |
| `DivisionPolynomial.lean:77, 96, 118, 141, 189, 239, 301, 306, 325, 346, 389, 394, 433, 485` | recursion seed `preNormEDS' … W.preΨ₄`; `preΨ'_four`; `Ψ_four`; `ψ_four`; `Φ_three/four`; `map_preΨ₄`; `baseChange_preΨ₄` |
| `ZSMul.lean:94, 112, 115, 123, 136` | `evalEval_preΨ₄`, `cusp_preΨ₄`, EDS evaluation glue |
| `DivisionPolynomialOmega.lean`, `LutzNagellTheorem/{PIDPrimeOrder,GeneralPrimeOrder}.lean` | downstream consumers of the division-polynomial tower |

Inline-derivation grep: **(none)** — call sites use `preΨ₄`; they don't re-derive its formula.

**Call-sites interpretation.** K ≥ 3 normally leans YES, *but the signal is inverted here*: these 21 uses depend on the **project's local copy** precisely because the fork **shadows the mathlib name within this project's import graph**. They are not evidence the object is novel — they are evidence the project re-rooted an entire mathlib subtree onto a forked EDS import. Every one of these call sites has an exact mathlib analogue (`WeierstrassCurve.preΨ₄` and the matching `natDegree_preΨ₄`, `map_preΨ₄`, `Ψ_four`, … are all in `…/DivisionPolynomial/Basic.lean` + `Degree.lean`).

---

### Composition check (Phase 6)

n/a — Phase 5 found the exact declaration in mathlib (identical body). No composition needed; the object *is* mathlib's `WeierstrassCurve.preΨ₄`.

Conclusion: **N/A (NO-mathlib-has-it short-circuits Phase 6).**

---

## Verdict: `WeierstrassCurve.preΨ₄`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): explicit degree-6 `b`-invariant formula is textbook-standard and matches the Lean body term-for-term; WebSearch also returns the official mathlib4 docs page for this exact `preΨ₄`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (`[CommRing R]`); no modern-idiom move (it already *is* the mathlib idiom).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.preΨ₄` at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:147` — **byte-for-byte identical** def, same namespace, same author, same docstring.
- Composition check (Phase 6): n/a (exact decl found).

**Rationale:**

This declaration is not a candidate for mathlib because **mathlib already contains it, identically**. The project's own module docstring states the file is "a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`", forked solely to import a local `EllipticDivisibilitySequence` (avoiding the `normEDS`/`complEDS` name collision with mathlib's version). The `preΨ₄` body in the project (`DivisionPolynomial.lean:70`) is character-for-character identical to mathlib's (`Basic.lean:147`), down to the `C`-coercions and the 2024 Angdinata copyright header. The literature (Silverman/Washington-style references, confirmed by WebSearch) gives precisely this degree-6 polynomial as the `ψ₄/ψ₂` cofactor, so there is no generalisation or modernisation gap either — and there couldn't be, because the project copied mathlib's already-modern formulation.

The 21 internal call sites are not a "real API → YES" signal here; they are an artifact of the fork shadowing the mathlib name within this project's import graph. Every consumer (degree lemmas, `map_`/`baseChange_`, the `Ψₙ`/`ψₙ`/`Φₙ` tower) has an exact mathlib counterpart in `…/DivisionPolynomial/Basic.lean` and `…/Degree.lean`.

**WHY not (refactor-actionable):**
Mathlib already has `WeierstrassCurve.preΨ₄` with the **identical** definition. The project does not need to (and should not try to) upstream it. The fork is a *workspace* concern, not a mathlib-content gap: the reason the local copy exists is the EDS-import name clash, which is a mathlib-internal naming issue (`normEDS`/`complEDS` defined in both `LutzNagell.EllipticDivisibilitySequence` and `Mathlib.NumberTheory.EllipticDivisibilitySequence`), **not** a missing-declaration issue.

- Existing mathlib decl:   `WeierstrassCurve.preΨ₄`
- Located at:              `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:147`
- Our form follows in 0 lines — it is the *same* declaration:
  ```lean
  example (R : Type*) [CommRing R] (W : WeierstrassCurve R) :
      W.preΨ₄ = 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 +
        10 * C W.b₈ * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2) :=
    rfl   -- holds for BOTH the project copy and mathlib's preΨ₄ (identical bodies)
  ```
- Call sites in our project (Phase 6.0): K ≈ 21 across 6 files.

**Refactor plan (workspace de-duplication, NOT a mathlib PR):**
This is a `/cleanup` cross-project dedup item, not a `/mathlibable` upstream. The whole forked `DivisionPolynomial.*` subtree should ideally be deleted in favour of mathlib's, *once the EDS name-collision is resolved*. Concretely:
1. Resolve the root cause: the local `LutzNagell.EllipticDivisibilitySequence` duplicates mathlib's `normEDS`/`complEDS`/`preNormEDS'`. Either (a) drop the local EDS copy and import `Mathlib.NumberTheory.EllipticDivisibilitySequence` directly, or (b) if the local EDS genuinely diverges, namespace it so it no longer shadows mathlib.
2. Once (1) is done, delete the project's `preΨ₄` (and the rest of the copied `DivisionPolynomial.lean` tower) and re-point all 21 call sites at mathlib's `WeierstrassCurve.preΨ₄` and its existing API (`natDegree_preΨ₄`, `coeff_preΨ₄`, `map_preΨ₄`, `baseChange_preΨ₄`, `Ψ_four`, `ψ_four`, `Φ_three`/`Φ_four`, all present in mathlib `Basic.lean`/`Degree.lean`). Argument/dot-notation order is unchanged (same names, same namespace).
3. Because the bodies are identical, the call sites need no proof changes — only the removal of the shadowing copy.

Note: per AINTLIB's CLAUDE.md, statement-touching cross-project dedup of a forked mathlib subtree is a coordinator/`/cleanup` concern; this report flags `preΨ₄` as one node of that larger dedup, with the EDS-import clash as the blocking prerequisite.

**Next action:** Do **not** open a mathlib PR. File/track a cleanup item to retire the forked `DivisionPolynomial.*` tree against mathlib's, gated on resolving the `EllipticDivisibilitySequence` `normEDS`/`complEDS` name collision; then delete the local `preΨ₄` and re-point its 21 call sites at `WeierstrassCurve.preΨ₄` from `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

---

## Next step

Do not upstream. Mathlib already has the identical `WeierstrassCurve.preΨ₄`. Track a workspace-dedup cleanup item (gated on the forked-EDS `normEDS`/`complEDS` name clash) to delete the local copy and re-point its 21 call sites at the mathlib decl.
