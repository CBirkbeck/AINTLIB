# /mathlibable report — `LutzNagell.PID.lutz_nagell_cubicDisc_discriminant`

### Baseline (Phase 0)
- lake build:               not run (env build stale; reasoned from source per instructions)
- decl `LutzNagell.PID.lutz_nagell_cubicDisc_discriminant`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:424`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Generalisation of the classical Lutz–Nagell theorem from ℤ/ℚ to a PID `R` of characteristic zero with fraction field `K`, and onward to number fields of class number 1.

Qualified name VERIFIED: namespaces `LutzNagell` (line 35) → `PID` (line 36), `end PID` at line 475. The decl is the `theorem lutz_nagell_cubicDisc_discriminant` at line 424 inside both, so the fully-qualified name is `LutzNagell.PID.lutz_nagell_cubicDisc_discriminant`. The prompt's parse is correct.

---

### Statement (Phase 1)

`lutz_nagell_cubicDisc_discriminant` is a theorem: the **Nagell–Lutz discriminant-divisibility step** for a Weierstrass curve in *medium* form `a₁ = a₃ = 0` (i.e. `y² = x³ + a₂x² + a₄x + a₆`) over a characteristic-zero PID `R` with fraction field `K`.

For a nonzero finite-order (torsion) point `(x, y)` on the base-changed curve over `K`, with integral coordinates `x₀, y₀ ∈ R` and the squarefree-at-torsion-primes hypothesis, the conclusion is

  `y₀ = 0  ∨  y₀² ∣ 4a₄³ + 27a₆² + 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆`.

The divisor is the **cubic discriminant** of `x³ + a₂x² + a₄x + a₆`. Indeed the Weierstrass discriminant in this case is `Δ = −16·(4a₄³ + 27a₆² + 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆)` (verified against the standard `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` with `b₂=4a₂, b₄=2a₄, b₆=4a₆, b₈=4a₂a₆−a₄²`; cross-checked against the project's own `shortCurveZ_delta : Δ = −16·(4A³+27B²)` for `a₂=0`). Specialising further to `a₂ = 0` gives the textbook `y₀² ∣ 4a₄³ + 27a₆²` — the classical Nagell–Lutz conclusion for `y² = x³ + Ax + B`.

Variables / typeclasses (Lean side):
- `R` : `CommRing`, `IsDomain`, `IsPrincipalIdealRing`, `CharZero` — the coefficient PID.
- `K` : `Field`, `DecidableEq`, `Algebra R K`, `IsFractionRing R K` — its fraction field.
- `W : WeierstrassCurve R` — the curve.

Hypotheses (Lean side):
- `ha₁ : W.a₁ = 0`, `ha₃ : W.a₃ = 0` — restricts to the medium model.
- `hpt : (curveK R K W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular affine point over `K`.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion.
- `hsf_all : ∀ p prime, p ∣ addOrderOf P → Squarefree (p : R)` — every prime dividing the torsion order is squarefree in `R` (the "unramified" hypothesis; vacuous over ℤ).
- `hx : algebraMap R K x₀ = x`, `hy : algebraMap R K y₀ = y` — the coordinates are integral, with integral lifts `x₀, y₀ ∈ R`.
- `hcurve : y₀² = x₀³ + a₂x₀² + a₄x₀ + a₆` — the integral curve equation.

Conclusion (math): a torsion point on the medium-form curve has `y₀ = 0` or `y₀²` divides the cubic discriminant.

Conclusion (Lean): `y₀ = 0 ∨ y₀ ^ 2 ∣ 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 + 4 * W.a₂ ^ 3 * W.a₆ − W.a₂ ^ 2 * W.a₄ ^ 2 − 18 * W.a₂ * W.a₄ * W.a₆`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a named theorem (Nagell–Lutz) and a stated main-result specialisation — the file's `## Main results` headline result `lutz_nagell_number_field_cubicDisc_discriminant` is its direct number-field wrapper (PIDMain.lean:554–570). Named-after-a-person theorems are, by the skill's definition, BIG.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def` — one-liner check n/a. (Body is a ~40-line `linear_combination` / `mul_dvd_mul`/`dvd_add` proof, PIDMain.lean:433–473; not a glue lemma.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)         | "Nagell-Lutz … y² divides 4A³+27B² discriminant torsion point elliptic curve"                            | yes  | `y² = x³+Ax+B`, torsion ⇒ `x,y∈ℤ` and `y=0` or `y² ∣ 4A³+27B²` | Wikipedia, HandWiki, UCI/UChicago lecture notes all give exactly this |
|  2 | WebSearch (general form)           | "general Weierstrass form … y² divides discriminant 2y+a₁x+a₃ … number field class number one"          | yes  | general `y²+a₁xy+a₃y=…`: torsion ⇒ `y=0` (order 2) or `y ∣ Δ` (so `y² ∣ Δ`) | Silverman-style general statement; matches the project's `κ₀ = 2y+a₁x+a₃` track exactly |
|  3 | WebSearch (named-after / extension)| Nagell-Lutz imaginary quadratic / number field class number one                                         | yes  | arXiv 2509.07524 "Nagell-Lutz Theorem for Imaginary Quadratic Fields with Class Number One" | the exact generalisation this project formalises (PID = ring of integers of class number 1) |
|  4 | ChatGPT MCP                        | standard form + generality + history                                                                    | n/a  | — | ChatGPT MCP unavailable in this env (noted in prompt); substituted by WebFetch on the arXiv source (row 3) + 3 WebSearches at different generalities |
|  5 | Local references                  | `ls .mathlib-quality/references/`, `refs/NagellLutz/`                                                    | n/a  | — | neither directory exists in this checkout — recorded n/a |
|  6 | nLab                              | Nagell-Lutz theorem                                                                                      | n/a  | — | nLab has no Nagell–Lutz / torsion-integrality page; not a category-theoretic concept |
|  7 | nCatLab                           | —                                                                                                       | n/a  | — | not a categorical concept |
|  8 | Stacks Project                    | Nagell-Lutz / torsion integrality                                                                        | n/a  | — | Stacks does not cover this arithmetic-of-elliptic-curves result |
|  9 | MathOverflow / Math.SE             | (covered via WebSearch general results)                                                                  | yes  | confirms `y ∣ D ⇒ y² ∣ D`; theorem is not an iff | consistent with the disjunction shape |
| 10 | arXiv (last 5 yrs)                | imaginary quadratic class number one Nagell-Lutz                                                         | yes  | arXiv 2509.07524 (2025) | uses **short** form `y²=x³+Ax+B`; conclusion there is *integrality* `x,y∈ℤ[√D]`; the divisibility step is the classical add-on |

WebFetch on arXiv 2509.07524 (the source paper): Theorem 1 uses `y² = x³ + Ax + B` with `A,B ∈ 𝒪_K`; its headline conclusion is integrality of the coordinates over the nine class-number-one imaginary quadratic fields. The `y² ∣ 4A³+27B²` divisibility is the standard companion statement to that integrality result.

### Literature summary (Phase 3)

Concept identified as: **the Nagell–Lutz theorem** (discriminant-divisibility half).
Sources agree on the standard form: **yes**. Two equivalent textbook framings:
  - *short* form `y² = x³ + Ax + B`: torsion ⇒ `y = 0` or `y² ∣ 4A³ + 27B²`;
  - *general* form `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`: torsion ⇒ `2y+a₁x+a₃ = 0` or `(2y+a₁x+a₃)² ∣ Δ` (equivalently `y ∣ Δ ⇒ y² ∣ Δ`).
Most general standard form: over a number field of class number one / a PID (so denominators are controlled), the general-Weierstrass `κ₀ = 2y+a₁x+a₃` statement — exactly the project's `lutz_nagell_pid_discriminant_of_torsion` (PIDMain.lean:401).
Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → ring of integers of class-number-one number field (arXiv 2509.07524) → general char-0 PID (this project — *the maximally general standard form*).
  - curve model: short `y²=x³+Ax+B` (most textbooks) → medium `a₁=a₃=0` (THIS decl) → full general Weierstrass (the project's `κ₀²∣4Δ` track).
Disagreement with the literature: **none**. The decl's cubic-disc expression `4a₄³+27a₆²+4a₂³a₆−a₂²a₄²−18a₂a₄a₆` is exactly `Δ/(−16)` for the `a₁=a₃=0` curve — the cubic discriminant of the RHS cubic.

---

### Generality analysis — `lutz_nagell_cubicDisc_discriminant` (Phase 4)

Literature-standard form (from Phase 3): over a class-number-one base, torsion ⇒ `2y+a₁x+a₃ = 0` or `(2y+a₁x+a₃)² ∣ Δ`, for the **full** general Weierstrass curve.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | `ha₁ : W.a₁ = 0`, `ha₃ : W.a₃ = 0` | medium model only | full general Weierstrass | **yes** | the project ALREADY proves the full form: `lutz_nagell_pid_discriminant_of_torsion` (line 401) gives `κ₀=0 ∨ κ₀²∣4Δ` with no `a₁/a₃` restriction. This decl is a *strict specialisation* of that. |
| 2 | `[IsPrincipalIdealRing R] [CharZero R]` | char-0 PID | ring of integers of class-number-1 field (arXiv) / PID | NO (in this track) | PID is the right level; matches the literature's "class number one" condition. Not a weakening target. |
| 3 | `hsf_all` (squarefree at torsion primes) | unramified hypothesis | needed off ℤ | NO | genuinely required away from ℤ; standard in the number-field generalisation. |
| 4 | conclusion: `y₀² ∣ cubicDisc` | cubic discriminant (`Δ/−16`) | `κ₀² ∣ Δ` | — | this is a cosmetic re-expression of the general conclusion under `a₁=a₃=0`, where `κ₀=2y₀` and `4·cubicDisc·(−4) = κ₀²`-scaled… i.e. derivable from #1 by `ring`/`dvd` bookkeeping. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (and narrower than the project's own general result).
Number of weakening opportunities found: 1 (the `a₁=a₃=0` restriction).
This decl is the *medium-model corollary* of the already-proved general theorem `lutz_nagell_pid_discriminant_of_torsion`. The literature/mathlib-idiomatic target is the **general-Weierstrass `κ₀²∣Δ` statement**, not this `a₁=a₃=0` cubic-disc reformulation.
Cost of restatement: n/a — the general form already exists in the file; this decl is a presentation convenience.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|---|---|---|---|
| 1 | bundled hyps → typeclasses? | no | the squarefree/PID hyps are genuine side-conditions, not class-able | — |
| 2 | sequences → filters? | no | no limiting/topological content | — |
| 3 | construct → universal property? | no | it's a divisibility theorem | — |
| 4 | set+closure → bundled substructure? | no | — | — |
| 5 | field-specific → weaker typeclass? | partial | already over a PID (general); fine | — |
| 6 | 1-categorical → higher? | no | — | — |
| 7 | concrete index → general structure? | **yes (in spirit)** | the *curve model* should be the general Weierstrass curve, with `Cubic.discr`/`WeierstrassCurve.Δ` used directly, rather than hard-coding `a₁=a₃=0` and a hand-expanded cubic polynomial | unifies with mathlib's `WeierstrassCurve.Δ` and `Cubic.discr` API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — the mathlib-idiomatic statement is the general-Weierstrass one phrased against `WeierstrassCurve.Δ` (the project's own `_of_torsion` form, `κ₀² ∣ 4·W.Δ`), not the `a₁=a₃=0` model with a literally-expanded degree-3 discriminant polynomial. The hand-expanded `4a₄³+27a₆²+…` should, for mathlib, be `WeierstrassCurve.Δ` (up to the `−16` unit) or `Cubic.discr`.
Real mathematical improvement: removes the artificial `a₁=a₃=0` restriction and the magic polynomial, reusing mathlib's discriminant API — one general theorem instead of a model-specific corollary.

---

### Mathlib search-status: `lutz_nagell_cubicDisc_discriminant` (Phase 5)

[A] Lean-Finder       (env lean index MCP not available)        n/a: tool not surfaced in this environment
[B] Loogle            (env lean index MCP not available)        n/a: tool not surfaced; substituted by [D]/[E] grep over the unpacked mathlib tree
[C] LeanSearch        (env lean index MCP not available)        n/a: tool not surfaced
[D] Grep mathlib src  "Nagell", "torsion ⇒ integral", "addOrderOf"+EllipticCurve, "IsOfFinAddOrder"  →  **no hit** for any Nagell–Lutz / torsion-integrality / `y²∣Δ` theorem. `addOrderOf`/"torsion" in `Weierstrass.lean` refer only to the **2-torsion polynomial** (roots = x-coords of 2-torsion), not to a finite-order-⇒-integral theorem. `Cubic.discr` exists (`Mathlib/Algebra/CubicDiscriminant.lean:461`); `WeierstrassCurve.Δ` exists (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`); `WeierstrassCurve.IsIntegral` *class* exists (`…/Reduction.lean:59`) but is a model-integrality predicate, unrelated to torsion.
[E] Name pattern      grep `lutz`, `nagell`, `cubicDisc` over `.lake/packages/mathlib`  →  **no hit**

Searched for both the user's `a₁=a₃=0` cubic-disc form AND the general `κ₀²∣Δ` form: mathlib has **neither**. Mathlib has the *building blocks* (`WeierstrassCurve.Δ`, division polynomials `Ψ`, `Cubic.discr`, the group law) but no Nagell–Lutz theorem of any flavour.

Concluded: **not in mathlib** (grep methods D+E exhausted across the whole mathlib tree, both the medium-model and the general form; the named theorem is absent).

---

### Composition check — `lutz_nagell_cubicDisc_discriminant` (Phase 6)

### Call sites
Internal use count: **1** (within the project, excluding the declaring file)
External-to-file callers: 1 distinct file (the same PIDMain.lean's NumberField namespace)

| Caller file:line | Usage pattern |
|---|---|
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:569` | `PID.lutz_nagell_cubicDisc_discriminant W ha₁ ha₃ hpt htor hsf_all hx hy hcurve` — the body of the number-field wrapper `lutz_nagell_number_field_cubicDisc_discriminant` |

Inline-derivation grep: the cubic-disc polynomial `4a₄³+27a₆²+…` is re-stated verbatim only in that one wrapper's *statement* (PIDMain.lean:566–568); it is not independently re-derived elsewhere. The substance lives in this PID lemma.

Call-sites signal: K = 1, used solely to forward into the number-field restatement. Per the skill's table, "K = 1 internal use only → possibly the wrong abstraction; lean toward NO-composable" — but here it is a deliberate PID→number-field layering, and the real point is that the *whole Nagell–Lutz development* (this is one specialisation node of it) is what would be upstreamed, not this single corollary in isolation.

### Composition check

Can `lutz_nagell_cubicDisc_discriminant` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: from mathlib primitives alone (`WeierstrassCurve.Δ`, `twoTorsionPolynomial`, division polynomials, group law).
  - Result: **fails**. There is no mathlib lemma asserting "finite-order point ⇒ `y²∣Δ`". Producing it requires the full Nagell–Lutz machinery the project builds over hundreds of lines (Ψ₃-divisibility from torsion, integrality at unramified primes, the `κ₀`↔`Ψ₂` bridge). This is a genuine theorem, not a composition.

Attempt 2: from the *project's own* general theorem `lutz_nagell_pid_discriminant_of_torsion` (line 401).
  - `rcases lutz_nagell_pid_discriminant_of_torsion …` then specialise `a₁=a₃=0` and convert `κ₀²∣4Δ` to `y₀²∣cubicDisc` via `ring`/`dvd` bookkeeping (a ~10-line `linear_combination` + `mul_dvd_mul`/`dvd_add` argument, PIDMain.lean:433–473).
  - Result: **succeeds, but this is a project-internal composition, not a mathlib one.** It shows the decl is a thin specialisation of the project's general result — relevant for upstreaming grain, not for a "mathlib already composes it" verdict.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib lacks the Nagell–Lutz core entirely). It IS a short specialisation of the project's *own* general theorem.

---

## Verdict: `LutzNagell.PID.lutz_nagell_cubicDisc_discriminant`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz is a classical named theorem; the maximally-general standard form is the general-Weierstrass `κ₀=0 ∨ κ₀²∣Δ` over a class-number-one base (= PID). The `a₁=a₃=0` cubic-disc form here is a strict specialisation. arXiv 2509.07524 confirms the class-number-one generalisation is current, live mathematics.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the `a₁=a₃=0` restriction is removable, and the project already proves the unrestricted form (`lutz_nagell_pid_discriminant_of_torsion`, line 401). Phase 4c: the mathlib-idiomatic statement uses `WeierstrassCurve.Δ`, not a hand-expanded cubic polynomial.
- Mathlib search (Phase 5): **not in mathlib** — no Nagell–Lutz theorem of any model exists; only building blocks (`WeierstrassCurve.Δ`, `Cubic.discr`, division polynomials, `IsIntegral` model class).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the Nagell–Lutz core is absent); it IS a ~10-line specialisation of the project's own general theorem.

**Rationale:**

Mathlib genuinely lacks the Nagell–Lutz theorem — this is real, missing, classical content (the gap is concrete: mathlib has `WeierstrassCurve.Δ`, `twoTorsionPolynomial`, `Cubic.discr`, division polynomials, the group law, and a `WeierstrassCurve.IsIntegral` *model* predicate, but **no** theorem connecting a finite-order point to integrality or to `y²∣Δ`). So the *development* this decl belongs to is squarely a YES for mathlib. But this *particular* declaration is the wrong grain: it hard-codes `a₁=a₃=0` and a literally-expanded degree-3 discriminant polynomial, when the project itself already proves the unrestricted general-Weierstrass statement `lutz_nagell_pid_discriminant_of_torsion` (`κ₀=0 ∨ κ₀²∣4Δ`, PIDMain.lean:401), of which this is a ~10-line `ring`/`dvd` specialisation. Mathlib's iron rule (most general form, and reuse `WeierstrassCurve.Δ` rather than a magic polynomial) says: upstream the general theorem, then — if a short-form corollary is wanted — derive `y²∣4A³+27B²` from it as a one-screen `example`/corollary stated against `WeierstrassCurve.Δ`, not against the spelled-out cubic. The verdict is therefore "generalise first": the thing to PR is the general `κ₀²∣Δ` result (the project's `_of_torsion` lemma), with this `a₁=a₃=0` cubic-disc form recovered as a thin corollary downstream.

Reason for the generalisation: **both** —
  - LITERATURE-WEAKENING: Phase 4b found the `a₁=a₃=0` restriction strictly narrower than the literature-standard general-Weierstrass form.
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c — phrase the conclusion via `WeierstrassCurve.Δ` / `Cubic.discr` instead of a hand-expanded polynomial.

Proposed restatement (the target to upstream — already exists in the project as `lutz_nagell_pid_discriminant_of_torsion`):
```lean
theorem nagell_lutz_discr
    {R K} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve R)
    {x y : K} (hpt : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hpt) → Squarefree (p : R))
    {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) :
    (2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 ∨
    (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 ∣ 4 * W.Δ := by
  sorry  -- = project's lutz_nagell_pid_discriminant_of_torsion
```
Estimated cost of regeneralisation: **CHEAP** — the general form is already proved in-file; "generalise first" here means *upstream the general lemma instead of this corollary*, and recover the cubic-disc / short-Weierstrass shapes as one-line `Δ`-rewrite corollaries.

Mathlib downstream this enables:
  - composes directly with `WeierstrassCurve.Δ` and its `Δ`-rewriting API, with `Cubic.discr` (`Mathlib/Algebra/CubicDiscriminant.lean`), and with the division-polynomial / 2-torsion-polynomial API in `Mathlib/AlgebraicGeometry/EllipticCurve/`.
  - gives the textbook `y²∣4A³+27B²` (short Weierstrass) and this `a₁=a₃=0` cubic-disc form as immediate corollaries, rather than as the primary statement.

Next action: run `/generalise LutzNagell.PID.lutz_nagell_pid_discriminant_of_torsion` (tensioning against both the general-Weierstrass literature form and the `WeierstrassCurve.Δ` modern idiom). Upstream THAT general theorem as the Nagell–Lutz contribution; keep `lutz_nagell_cubicDisc_discriminant` as a project-side / downstream corollary (or a short `example`) rather than a mathlib-primary declaration.

---

## Next step

Run `/generalise` on the general theorem `lutz_nagell_pid_discriminant_of_torsion` and upstream that (the maximal-generality Nagell–Lutz divisibility statement, phrased with `WeierstrassCurve.Δ`); recover this `a₁=a₃=0` cubic-discriminant form, and the classical short-Weierstrass `y²∣4A³+27B²`, as thin corollaries downstream rather than as standalone mathlib declarations.
