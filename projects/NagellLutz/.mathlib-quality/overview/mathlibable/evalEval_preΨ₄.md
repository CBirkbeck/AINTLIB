# /mathlibable report — `WeierstrassCurve.Universal.evalEval_preΨ₄`

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task brief; reasoning from source + mathlib tree on pin `d90090f`)
- decl `WeierstrassCurve.Universal.evalEval_preΨ₄`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:94`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Proves `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coords via the universal Weierstrass curve over `ℤ[A₁..A₆]`; this file bridges universal division polynomials to their evaluations at a concrete point `(x,y)`.

Qualified name VERIFIED from source: the lemma sits inside `namespace WeierstrassCurve` (ZSMul.lean:76) → `namespace Universal` (ZSMul.lean:86), so the fully-qualified name is **`WeierstrassCurve.Universal.evalEval_preΨ₄`**.

---

### Statement (Phase 1)

```lean
lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]
```

In prose: Let `W : WeierstrassCurve R` be an arbitrary Weierstrass curve over a commutative ring `R`,
with `x y : R`. Let `curve : WeierstrassCurve (MvPolynomial Coeff ℤ)` be the **universal Weierstrass
curve** whose coefficients `a₁,…,a₆` are the free generators `A₁,…,A₆` of `ℤ[A₁,A₂,A₃,A₄,A₆]`. Then
the value at `(x,y)` of (the constant-in-`Y` bivariate lift of) the curve's own auxiliary 4-division
polynomial `W.preΨ₄ ∈ R[X]` equals the result of taking the *universal* `curve.preΨ₄`, specialising it
to `W` (sending `Aᵢ ↦ W.aᵢ`) via the curve-evaluation homomorphism `polyEval W x y`, and evaluating
at `(x,y)`. Equivalently: **the auxiliary division polynomial `preΨ₄` commutes with specialisation of
the universal curve.**

Variables / typeclasses involved (Lean side):
- `{R : Type*} [CommRing R]` — base ring of the concrete curve.
- `(W : WeierstrassCurve R)` — the concrete curve.
- `{x y : R}` — coordinates of a point on the affine plane over `R`.
- `curve : WeierstrassCurve (MvPolynomial Coeff ℤ)` — the **project-local** universal Weierstrass curve (`Universal.lean:84`).
- `polyEval W x y : Poly →+* R` — **project-local** evaluation hom from `ℤ[A₁..A₆,X,Y]` to `R` (`Universal.lean:203`), built from `W.specialize` (`Universal.lean:190`).

Hypotheses (Lean side): none (universally quantified over `R, W, x, y`).

Conclusion (math): `preΨ₄` of the universal curve, specialised to `W` and evaluated at `(x,y)`, equals `preΨ₄(W)` evaluated at `(x,y)`.

Conclusion (Lean): `(C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄)` (an equality in `R`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A glue/compatibility lemma (one-line `simp_rw` proof) bridging two project-local definitions (`evalEval` of a curve's own `preΨ₄` vs. `polyEval` of the universal `preΨ₄`). Not a named theorem, not a new structure, not a `## Main results` entry.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line *definition* check is **n/a**. (The proof body is one line, which is recorded as a SMALL/glue signal, but the 2b def-exemption table does not apply to lemmas.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | universal elliptic curve division polynomials specialization ring homomorphism Weierstrass coefficients | yes  | division polys ∈ `ℤ[a₁,a₂,a₃,a₄,a₆,x,y]`, designed to work functorially across rings via ring homs | arXiv 1303.4327 (homogeneous division polys); MIT 18.783 notes 5/6; mathlib4 docs |
|  2 | WebSearch (general form)         | "division polynomial" specialization "universal" Weierstrass curve evaluation Nagell-Lutz               | yes  | division polys form the **generic** EDS over `ℚ[x,y,A,B]/(y²-x³-Ax-B)`; specialise by plugging in `A,B` and working in the coordinate ring | Wikipedia "Division polynomials"; Stange (eprint 2025/521); no *named* "evalEval-commutes" lemma surfaced |
|  3 | WebSearch (named-after / aliases)| elliptic divisibility sequence universal Weierstrass curve Z[a1,a2,a3,a4,a6] formalization Lean mathlib  | yes  | mathlib defines `ψₙ` as the normalised EDS; "universal smooth Weierstrass curve = complement of discriminant" exists as a *scheme* in the literature | confirms mathlib has `preΨ`, `map_preΨ`; universal *curve* exists in lit but the specialisation-commutes plumbing is internal |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to WebSearch ×3 + direct mathlib source read)                      | n/a  | —                                | substituted by the three distinct-generality WebSearches above + direct reading of mathlib's `DivisionPolynomial/Basic.lean` |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                | n/a  | (no references dir)              | directory absent — recorded n/a |
|  6 | nLab                             | "universal elliptic curve" / "division polynomial"                                                     | n/a  | universal elliptic curve = moduli-stack object; nLab has no *specialisation-of-preΨ₄* lemma | concept is moduli-theoretic there, not this evaluation identity |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | not a categorical concept (a polynomial-evaluation identity) |
|  8 | Stacks Project (if alg geom)     | universal Weierstrass / division polynomial                                                            | n/a  | Stacks treats Weierstrass models / moduli but not named division-polynomial specialisation lemmas | not a Stacks-level statement |
|  9 | MathOverflow / Math.StackExchange| division polynomials over `ℤ[a_i]` specialisation                                                       | yes  | community consensus: division polys are *defined* over the universal ring `ℤ[a₁..a₆]` and specialised by ring homs — exactly the project's design | confirms the *design pattern* is standard; the bridging lemma itself is unremarked plumbing |
| 10 | recent arXiv (last 5 years)      | division polynomials arbitrary isogenies / formal group (Stange 2025; Best–… formal EC group law 2023) | yes  | Stange eprint 2025/521; arXiv 2302.10640 (formal proof of EC group law) | universal-ring construction is the modern standard; no paper names this `evalEval`-commutes identity |

The protocol passes: WebSearch ran 3 distinct-generality queries (specific / generic-EDS / formalization); ChatGPT MCP unavailable and substituted per the task brief by extra WebSearch + direct mathlib-source reading; local refs absent (n/a); nLab / nCatLab / Stacks / MathOverflow / arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **specialisation (base change) of a division polynomial from the universal Weierstrass curve to a concrete one** — i.e. naturality of `preΨ₄` under the ring homomorphism `ℤ[A₁..A₆] → R, Aᵢ ↦ aᵢ`.
Sources agree on the standard form: **yes** — the literature uniformly *defines* division polynomials over the universal coefficient ring `ℤ[a₁,a₂,a₃,a₄,a₆,x,y]` (or `ℚ[x,y,A,B]/(…)`) and recovers any concrete curve by specialising coefficients via a ring homomorphism. That a division polynomial commutes with such a specialisation is treated as self-evident, never as a named theorem.
Most general standard form: division polynomials are functorial in the base ring: for any ring map `f : R → S` carrying `W` to `W'`, `preΨ₄(W')= f∘preΨ₄(W)` (mathlib's `map_preΨ₄`). The "universal → concrete" specialisation is the special case `f = W.specialize`.
Generality dimensions where the literature varies:
  - base ring: from `ℚ[x,y,A,B]/(…)` (short Weierstrass) up to `ℤ[a₁..a₆,x,y]` (general Weierstrass, mathlib's choice). The most general is the general-Weierstrass `ℤ[a₁..a₆]`, which both mathlib and the project use.
  - the *carrier* of naturality: literature says "specialise coefficients"; mathlib makes it the single naturality lemma `map_preΨ₄` over an arbitrary ring hom. The project instead routes it through a bespoke `Universal.curve` + `specialize` + `polyEval` tower.
Disagreement with the literature: none mathematically. The disagreement is *organisational*: mathlib (and the literature's "just specialise coefficients") obtains this content directly from the single naturality lemma `map_preΨ₄`, whereas the project re-expresses it through an extra `Universal.curve`/`polyEval` scaffold and then needs this `evalEval_*` family of bridging lemmas to climb back down.

---

### Generality analysis — `WeierstrassCurve.Universal.evalEval_preΨ₄`

Literature-standard form (from Phase 3): naturality of `preΨ₄` under base change — already `map_preΨ₄` in mathlib, `(W.map f).preΨ₄ = W.preΨ₄.map f`, for an *arbitrary* ring hom `f`.

| # | Parameter / hypothesis            | Current Lean form                          | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`                    | commutative ring                           | commutative ring                 | NO                  | already maximally general for division polynomials |
| 2 | the source curve                  | the *fixed* universal `curve` over `ℤ[A₁..A₆]` | an arbitrary curve + arbitrary ring hom | yes (already in mathlib) | mathlib's `map_preΨ₄` is stated for *any* `f : R →+* S`; specialising to the universal curve + `W.specialize` is strictly narrower |
| 3 | the specialising hom              | the *fixed* `W.specialize` / `polyEval W x y` | an arbitrary ring hom            | yes (already in mathlib) | the lemma hard-codes the universal-curve specialisation; the general naturality is what mathlib already exposes |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the universal-curve special case of `map_preΨ₄`, additionally wrapped in `evalEval`/`polyEval` evaluation at `(x,y)`.
Number of weakening opportunities found: 2 (arbitrary curve, arbitrary ring hom) — but **both are already realised by mathlib's `map_preΨ₄`**, so the "generalisation" is not a new contribution; it is *the existing mathlib lemma*. Hence this does not point to YES-but-generalise-first; it points to the content already being in mathlib in more general form.
Proposed restatement: n/a — the general form is `WeierstrassCurve.map_preΨ₄`, which already exists.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | — | already a plain naturality identity |
|  2 | sequences/metric → filters/topology? | no | — | no topology involved |
|  3 | construct → universal-property class? | no | — | — |
|  4 | set+closure-pred → bundled substructure? | no | — | — |
|  5 | vector-space/field-specific → weaken typeclass? | no | — | already over an arbitrary `CommRing` |
|  6 | 1-categorical → higher-categorical? | no | — | — |
|  7 | concrete index → general additive structure? | no | — | the only "index" is the fixed `preΨ₄`; no generalisation move |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — this is a base-change naturality identity over an arbitrary `CommRing`, already maximally idiomatic in mathlib's terms (mathlib expresses it as `map_preΨ₄`). There is no contemporary-idiom restatement that improves organisation; the *more* idiomatic move is to not have the `Universal.curve` scaffold at all and use `map_preΨ₄` directly.

---

### Diamond / defeq risk — n/a (declaration kind is `lemma`)

Phase 4.5 is skipped: lemmas introduce no definitional equalities or typeclass-search paths.

---

### Mathlib search-status: `WeierstrassCurve.Universal.evalEval_preΨ₄`

[A] Lean-Finder        "division polynomial preΨ₄ specialize / evalEval"   no exact hit; surfaces `WeierstrassCurve.preΨ₄`, `map_preΨ₄`
[B] Loogle             `(Polynomial.evalEval _ _ (Polynomial.C (WeierstrassCurve.preΨ₄ _)))` — no decl in mathlib mentions a `Universal.curve`; pattern `(WeierstrassCurve.map _ _).preΨ₄ = _` hits `map_preΨ₄`   building block found
[C] LeanSearch         "preΨ₄ commutes with base change / specialization of Weierstrass curve"   hits `WeierstrassCurve.map_preΨ₄`
[D] Grep mathlib src   `grep -rn "Universal" …/EllipticCurve/` → only `UniversallyOpen.lean` (unrelated). `evalEval_ψ/φ/ω/Ψ₃/preΨ₄` → **0 hits** in mathlib. `map_preΨ₄` → present at `DivisionPolynomial/Basic.lean:433` (`@[simp]`)   no `Universal.curve`/`polyEval`/`specialize` framework in mathlib; the `evalEval_*` family is project-only
[E] Name pattern       `evalEval_preΨ₄`, `Universal.curve`, `polyEval`, `specialize` (curve)   project-only names; not in mathlib

Searched for both:
  - the user's current form (`evalEval`/`polyEval` of universal `preΨ₄`) → **not in mathlib** (no `Universal.curve` machinery exists there).
  - the literature-standard / general form (naturality of `preΨ₄` under base change) → **found in mathlib as `WeierstrassCurve.map_preΨ₄`** at `DivisionPolynomial/Basic.lean:433`, `@[simp]`, for an arbitrary ring hom.

Concluded: **"found building blocks (`WeierstrassCurve.map_preΨ₄`, plus mathlib's `Polynomial.eval₂_eval₂RingHom_apply` / `map_C` / `coe_mapRingHom`); composition (together with the project-local `polyEval`/`map_specialize`) yields our form."** The exact statement is **not** in mathlib and **cannot** be — it is phrased against the project-only `Universal.curve` / `polyEval` scaffold, which mathlib deliberately does not have (mathlib obtains the same content directly from `map_preΨ₄`).

---

### Call sites — `WeierstrassCurve.Universal.evalEval_preΨ₄`

Internal use count: **2** (within NagellLutz, excluding the declaring file's own line):
- `ZSMul.lean:115` — in `polyEval_cusp_ψ` (`rw [… ← evalEval_preΨ₄, …]`)
- `ZSMul.lean:123` — in `polyEval_cusp_ψc` (`rw [… ← evalEval_preΨ₄]`)

External-to-file callers: both uses are in the *same file* (`ZSMul.lean`) as the declaration. **0** distinct other files inside NagellLutz.

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| LutzNagell/ZSMul.lean:115      | `rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, …]` |
| LutzNagell/ZSMul.lean:123      | `rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - **Cross-project DUPLICATE:** `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:169` declares a **verbatim-identical** `evalEval_preΨ₄` (same statement, same proof), used at HasseWeil lines 190 & 199. Both NagellLutz and HasseWeil forked the same `Universal.curve` track. This is a monorepo-consolidation signal (dedup candidate), not a mathlib signal.

Call-sites reading: the lemma is real local API — used to discharge the `cusp` base case where the universal `ψ`/`ψc` are evaluated at the node `(1,1)` of the cuspidal curve — but it is used **only inside its own file**, both uses being `rw [← evalEval_preΨ₄]` rewrites in `simp`-style chains. That is the profile of an internal rewrite helper, not a reusable public theorem.

---

### Composition check (Phase 6)

Can `evalEval_preΨ₄` be derived from mathlib (+ the project's own `polyEval` unfolding) in ≤3 chained calls?

Attempt 1 (the actual proof): `simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]`
  - Mathlib decls used: `WeierstrassCurve.map_preΨ₄` (the load-bearing one), `Polynomial.map_C`, `Polynomial.coe_mapRingHom`, and `polyEval_apply` (which is `Polynomial.eval₂_eval₂RingHom_apply`).
  - Project-local decls used: `polyEval`/`polyEval_apply`, `map_specialize` (both unavoidable — they *are* the scaffold the lemma is phrased in).
  - Result: **succeeds** — this is the existing one-line proof.
  - Notes: The entire mathematical content is the single rewrite `← map_preΨ₄` (specialisation commutes with `preΨ₄`); everything else is unfolding the project's `polyEval`/`evalEval` definitions and `map_C`/`coe_mapRingHom` bookkeeping.

Conclusion: **COMPOSABLE** — `map_preΨ₄` (mathlib, `@[simp]`) + `map_C` + `coe_mapRingHom` + `polyEval_apply`/`map_specialize` (project glue), a ≤3-substantive-step `simp_rw`. No new *mathematical* lemma is needed; the only reason a separate declaration exists is to package the unfolding for the two `rw [← …]` sites.

---

## Verdict: `WeierstrassCurve.Universal.evalEval_preΨ₄`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the content is "division polynomials are defined over the universal ring `ℤ[a₁..a₆]` and specialised by ring homomorphisms" — a *design pattern*, never a named theorem. The naturality it encodes is mathlib's `map_preΨ₄`.
- Generality analysis (Phase 4): STRICTLY NARROWER — it is the universal-curve special case of base-change naturality, and that general form already exists in mathlib (`map_preΨ₄`). No modern-idiom improvement (4c: none).
- Mathlib search (Phase 5): exact form **not** in mathlib (depends on project-only `Universal.curve`/`polyEval`); the general building block **is** in mathlib as `WeierstrassCurve.map_preΨ₄` (`DivisionPolynomial/Basic.lean:433`, `@[simp]`).
- Composition check (Phase 6): COMPOSABLE — one-line `simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]`.

**Rationale:**

`evalEval_preΨ₄` is not a self-contained mathematical statement that could live in mathlib: it is phrased against the project's bespoke `Universal.curve` (the universal Weierstrass curve over `MvPolynomial Coeff ℤ`), `specialize`, and `polyEval` scaffolding, none of which exists in mathlib. Mathlib deliberately formalises division-polynomial naturality *directly* — as the single `@[simp]` lemma `WeierstrassCurve.map_preΨ₄`, `(W.map f).preΨ₄ = W.preΨ₄.map f` for an arbitrary ring homomorphism `f` — rather than by routing through a universal curve and then climbing back down with a family of `evalEval_*` bridging lemmas. So mathlib already has the *content* (in strictly greater generality), and this lemma is the project-internal specialisation-plus-evaluation wrapper around it. Its proof is literally `← map_preΨ₄` plus definitional unfolding of `polyEval`/`evalEval`.

Because the lemma is stated in project-only vocabulary, the honest bucket is NO-composable-from-mathlib rather than NO-mathlib-has-it: you cannot point at a single mathlib decl whose statement *is* this one (the statement mentions `Universal.curve`), but you can derive this statement in ≤3 mathlib-backed steps the instant you unfold the project's own `polyEval`. The lemma earns its keep purely as an internal rewrite helper for the two `rw [← evalEval_preΨ₄]` sites in the cusp base-case proof — both in its own file. (Note also the verbatim cross-project duplicate in HasseWeil; that is a monorepo dedup concern, handled on `main`, orthogonal to mathlib-ability.)

**WHY not (refactor-actionable):**
Mathlib has the building block; the lemma is the universal-curve evaluation wrapper around `map_preΨ₄`. The reason it is not mathlib material is structural: mathlib has chosen *not* to carry a `Universal.curve`/`specialize`/`polyEval` framework, so there is no home in mathlib for a lemma whose very statement names that framework. The `Universal.*` tower is a project design decision for the Nagell-Lutz / Hasse-Weil developments, not a gap in mathlib.

Mathlib building blocks:
- `WeierstrassCurve.map_preΨ₄` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:433` (`@[simp]`), the naturality `(W.map f).preΨ₄ = W.preΨ₄.map f`.
- `Polynomial.map_C`, `Polynomial.coe_mapRingHom` — `Mathlib/Algebra/Polynomial/…`.
- `Polynomial.eval₂_eval₂RingHom_apply` — the lemma behind the project's `polyEval_apply`.

Composition sketch (≤3 substantive lines — this *is* the existing proof):
```lean
example {R} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]
```

Call sites in our project (from Phase 6.0): K = 2 (both in `ZSMul.lean`, lines 115 & 123).

Refactor plan (project-internal — NOT a mathlib action):
- Do **not** attempt to upstream `evalEval_preΨ₄`: its statement is in project-only vocabulary, so there is nothing to add to mathlib. The upstreamable content (`map_preΨ₄`) is already there.
- This lemma should be **kept as a local helper** as long as the `Universal.curve` proof strategy is in use — it is correctly factored for its two `rw [← …]` consumers. It is not "delete and inline" in the usual NO-composable sense, because inlining a 4-rewrite `simp_rw` into the two `rw` chains would be a net readability loss; the abstraction is locally justified.
- **Consolidation action (separate from mathlib-ability):** deduplicate against the verbatim copy `WeierstrassCurve.Universal.evalEval_preΨ₄` in `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:169` — both projects should import a single shared copy (candidate `Common/`), rather than each forking the `Universal` track. File this as a monorepo cleanup ticket on `main`, not a mathlib PR.

**Bottom line for mathlib:** nothing to do. The general fact is already in mathlib (`map_preΨ₄`); this is a project-local evaluation wrapper.

---

## Next step

No mathlib action. Keep `evalEval_preΨ₄` as a project-internal rewrite helper (its content is mathlib's `WeierstrassCurve.map_preΨ₄` specialised to the universal curve). Separately, on `main`, file a consolidation ticket to dedup the verbatim copy in HasseWeil (`HasseWeil/Auxiliary/DivisionPolynomial.lean:169`) into a single shared declaration.
