# /mathlibable report — `LutzNagell.PID.x_isInteger_of_odd_prime_torsion_squarefree`

### Baseline (Phase 0)
- lake build:               not run (sandbox build stale per task brief; reasoned from source + present mathlib package)
- decl `LutzNagell.PID.x_isInteger_of_odd_prime_torsion_squarefree`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:113`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Prime-order torsion integrality for Weierstrass curves over UFDs — generalizes `GeneralPrimeOrder.lean` from ℤ/ℚ to a UFD `R` with fraction field `K`.

True qualified name **confirmed** from source: namespace `LutzNagell.PID` (lines 24–25), base name `x_isInteger_of_odd_prime_torsion_squarefree` (line 113). Matches the parsed name.

---

### Statement (Phase 1)

`x_isInteger_of_odd_prime_torsion_squarefree` states: let `W` be a Weierstrass curve over a UFD `R` (an `IsDomain` + `UniqueFactorizationMonoid`) with fraction field `K`. Let `P = (x, y)` be a nonsingular `K`-point of `W`. If `p` is an **odd prime** (natural number), `p·P = 0` in the Jacobian point group (i.e. `P` is `p`-torsion), and the image `(p : R)` is **squarefree** in `R`, then the `x`-coordinate is integral: `x ∈ R` (`IsLocalization.IsInteger R x`).

This is the "x-coordinate is an integer" half of the **Nagell–Lutz theorem**, specialized to odd prime order and generalized from the base ring ℤ to an arbitrary UFD under the extra hypothesis that `p` does not "ramify" (is squarefree) in `R`.

Variables / typeclasses (Lean side):
- `R` : a UFD (`CommRing`, `IsDomain`, `UniqueFactorizationMonoid`) — the ring of "integers".
- `K` : `Field`, `DecidableEq`, fraction field of `R` (`IsFractionRing R K`) — the "rationals".
- `W : WeierstrassCurve R` — an integral Weierstrass model.

Hypotheses (Lean side):
- `hns : (curveK R K W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular point of the base-changed curve over `K`.
- `hp : p.Prime`, `hodd : p ≠ 2` — `p` is an odd prime.
- `htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0` — `p`-torsion.
- `hsf : Squarefree (p : R)` — the key "unramified" hypothesis.

Conclusion (math): the `x`-coordinate lies in `R`.
Conclusion (Lean): `IsLocalization.IsInteger R x`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is an essential intermediate step of a **named theorem** (Nagell–Lutz), and is named in this project's `## Main results` framing as the connective tissue between the abstract `isInteger_of_root_squarefree_leading_coeff` and the concrete division-polynomial torsion setting. Named-after-a-person theorems are essentially guaranteed to be near the literature.

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a**. (The proof body is a ~20-line multi-step assembly, not a one-liner.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Nagell-Lutz theorem torsion points integer coordinates elliptic curve division polynomial proof" | yes | Rational torsion point on `E/ℚ` (integral Weierstrass) has integer coords; `y=0` or `y²∣D` | Wikipedia, AIMS essay, U.Chicago REU (Galperin). No "squarefree-`p`" abstraction. |
| 2 | WebSearch (general form) | "Nagell-Lutz generalization … Dedekind domain number field torsion integral squarefree ramification" | partial | Generalizes to arbitrary number fields (Cassels 1976); quadratic/cubic field torsion enumerations (1989/1990/1997); arXiv 2509.07524 (imaginary quadratic, class number 1) | Standard generalizations exist over number fields, but **none** stated via a per-prime "squarefree `(p:R)`" UFD hypothesis. |
| 3 | WebSearch (named-after / route) | "Silverman Arithmetic of Elliptic Curves torsion integral formal group reduction p-adic VIII Nagell-Lutz" | yes | Silverman VII–VIII: integrality of torsion via **formal groups / reduction mod p**, not the squarefree-leading-coeff route | The textbook-standard *proof* of the number-field generalization is formal-group/reduction, distinct from this project's division-polynomial route. |
| 4 | ChatGPT MCP | (3 questions: standard-form? reusable-named-lemma? more-general statement?) | **n/a — server down** | — | Codex MCP failed to launch (sandbox); fell back to WebSearch + WebFetch + source reasoning, per task brief. |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/references/` | n/a | (directory absent) | No refs dir for this project. |
| 6 | nLab | "Nagell-Lutz" / elliptic curve torsion integrality | no | — | nLab has no Nagell–Lutz / torsion-integrality page; not a categorical concept. |
| 7 | nCatLab | (same) | n/a | — | Not a categorical concept. |
| 8 | Stacks Project | elliptic curve torsion integral points | n/a | — | Stacks has no elliptic-curve Nagell–Lutz / torsion-integrality material; out of scope. |
| 9 | MathOverflow / MSE | "Nagell-Lutz" generality / squarefree primes | partial (via #1/#2 result sets) | confirms the ℤ statement + number-field generalizations | No source packages the result with a "squarefree `(p:R)`" hypothesis. |
| 10 | recent arXiv (≤5y) | Nagell-Lutz imaginary quadratic / Dedekind | yes | arXiv 2509.07524 "Nagell-Lutz for Imaginary Quadratic Fields with Class Number One" (2025) | Active topic; still stated over specific number rings, proof via standard reduction, not this bespoke UFD-squarefree intermediate. |

The protocol passed: WebSearch ran ≥3 queries at distinct generality levels (specific ℤ form, Dedekind/number-field generalization, the Silverman proof-route); local refs checked (absent); nLab/Stacks/nCatLab/MathOverflow/arXiv each checked or recorded `n/a` with reason. ChatGPT MCP attempted but the server failed to launch (recorded `n/a`, fallbacks used as the task brief directs).

### Literature summary (Phase 3)

Concept identified as: the **integer-coordinates (integrality) half of the Nagell–Lutz theorem**, restricted to **odd prime order** and generalized to a UFD base ring `R` under the hypothesis that `(p:R)` is squarefree.

Sources agree on the standard form: **yes** for the classical statement (torsion ⟹ integral over ℤ; number-field generalizations exist). **No** source states it with the project's "`(p:R)` squarefree" / per-prime UFD packaging — that framing is bespoke to this formalization.

Most general standard form: "On an elliptic curve over a number field `K` in integral Weierstrass model, a torsion point is integral (lies in `𝒪_K`)" — proved in the literature via **reduction mod a prime / formal groups**, with refinements (and the precise denominators allowed) depending on ramification. The "x-coordinate denominator divides the division-polynomial leading coefficient `= p`" argument is the classical **ℤ** route; the squarefree hypothesis is what lets it run over a general UFD without localizing at one prime.

Generality dimensions where the literature varies:
- **Base ring**: ℤ (classical) → ring of integers of a number field / Dedekind domain (generalizations). This decl sits at "UFD with a squarefree-`p` hypothesis", which is **between** ℤ and the full Dedekind-domain statement.
- **Proof route**: division polynomials + rational root theorem (this decl, classical-ℤ-style) vs. formal groups / reduction mod p (Silverman, number-field generalizations).
- **Order**: this decl handles **odd prime** order only (order 2 and order 4 are separate theorems in the same file).

Disagreement with the literature: the literature does not isolate this exact intermediate lemma, nor use the "squarefree `(p:R)`" hypothesis. It is a project-internal decomposition of the Nagell–Lutz proof.

---

### Generality analysis — `x_isInteger_of_odd_prime_torsion_squarefree`

Literature-standard form (from Phase 3): "torsion point on integral Weierstrass model over `𝒪_K` ⟹ integral", proved via reduction/formal groups, with no squarefree hypothesis.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[UniqueFactorizationMonoid R]` | UFD | Dedekind domain / `𝒪_K` (not nec. UFD) | conceptually yes | The full Nagell–Lutz generalization holds over any Dedekind domain (work prime-by-prime). But this proof route uses global unique factorization + the rational root theorem; dropping UFD would need the formal-group/reduction route — EXPENSIVE, a different proof. Not a mechanical weakening. |
| 2 | `hsf : Squarefree (p : R)` | `p` squarefree (unramified) in `R` | (no such hypothesis in the literature; replaced by per-prime/formal-group analysis) | NO (within this route) | The squarefree hypothesis is exactly what makes "denominator has no repeated prime factor ⟹ denominator is a unit" work. Removing it requires bounding denominators by powers of ramified primes (the `den_dvd_of_order_two`-style results in the same file) — genuinely different conclusion, not a weakening of *this* statement. |
| 3 | `hodd : p ≠ 2` | odd prime | all primes / all orders | NO (here) | Order 2 / order 4 handled by sibling theorems (`integrality_of_order_four_squarefree`, `den_dvd_of_order_two`) because the division polynomial `ψ_p` is no longer a polynomial in `x` alone for even `p`. Not weakenable in-place. |
| 4 | `{x y : K}` with `IsFractionRing R K` | fraction field | — | NO | This is the natural setting; already maximally general for the "rationals over `R`". |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along the base-ring axis (UFD-with-squarefree-`p` vs. the Dedekind/number-field standard), but it is **NOT a mechanical weakening away** from a more general form: the more general statement requires a fundamentally different proof (formal groups / reduction mod p), and the squarefree hypothesis is load-bearing for the chosen route, not a removable convenience.

Number of *mechanical* weakening opportunities found: 0.
Proposed restatement: none that is CHEAP/MODERATE. A Dedekind-domain / number-field version is a separate development (EXPENSIVE, new proof), not a regeneralization of this theorem.

Cost of restatement to literature-standard: **EXPENSIVE — proof needs new ideas** (formal groups / reduction). This is flagged for the verdict, not used to downgrade it.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | Already fully typeclass-driven (`UniqueFactorizationMonoid`, `IsFractionRing`). | — |
| 2 | sequences/metric → filters/topological? | no | No analytic content; purely algebraic. | — |
| 3 | construct object → universal-property class? | no | It is a theorem (a `Prop`), nothing constructed. | — |
| 4 | set-with-closure → bundled substructure? | no | No substructure here. | — |
| 5 | vector-space/field-specific → weaken typeclasses? | partial | Base ring is already as weak as the *route* allows (UFD); see 4b row 1. The genuine generalization (Dedekind) is a different proof, not an idiom swap. | — |
| 6 | 1-categorical → higher-categorical? | no | Not categorical. | — |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | already done | This *is* the generalization of the ℤ version (`x_integral_of_odd_prime_torsion_general`) to a general UFD `R`. The index-generalization move has already been applied. | unifies with the General-track ℤ/ℚ theorem |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (in the "cheap reformulation" sense). The decl is already the typeclass-generalized (UFD) form of the concrete ℤ/ℚ theorem; the only further generalization (Dedekind/number-field) is a different proof, captured under Phase 4b as EXPENSIVE, not a modernisation swap.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `x_isInteger_of_odd_prime_torsion_squarefree`

[A] Lean-Finder       n/a (sandbox; used grep over the present mathlib package + WebSearch for known mathlib decls)
[B] Loogle            type-pattern `WeierstrassCurve _, IsLocalization.IsInteger _ _` / torsion ⟹ integer — no hits (mathlib has no torsion-integrality lemma)
[C] LeanSearch        "torsion point elliptic curve integer coordinates" / "Nagell Lutz" — no hits in mathlib
[D] Grep mathlib src  `nagell|lutz|torsion.*integ|isInteger` in `AlgebraicGeometry/EllipticCurve/` → **none** (only NumberField unit-`torsion`, unrelated); `den_dvd_of_is_root|isInteger_of_is_root_of_monic|isInteger_of_isUnit_den` → **present** in `RingTheory/Polynomial/RationalRoot.lean`; `leadingCoeff_preΨ|preΨ` → **present** in `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`
[E] Name pattern      grep for `x_isInteger_of_odd_prime`, `prime_order_integrality`, `den_no_simple_prime` in mathlib → none

Searched for both:
  - the user's current form (UFD, squarefree `p`, odd prime torsion ⟹ `IsInteger`): **not in mathlib**.
  - the literature-standard form (torsion over `𝒪_K` ⟹ integral): **not in mathlib** — mathlib has **no Nagell–Lutz theorem and no elliptic-curve torsion-integrality result at all**. (Confirmed: zero `IsInteger`/integral-point hits across the entire `AlgebraicGeometry/EllipticCurve/` tree.)

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib *does* provide the **building blocks** — the rational-root-theorem primitives (`den_dvd_of_is_root`, `isInteger_of_isUnit_den`, `isInteger_of_is_root_of_monic`) and the full division-polynomial API (`preΨ`, `WeierstrassCurve.leadingCoeff_preΨ`, `evalEval_ψ_odd`, `WeierstrassCurve.map_preΨ`) — but **not** the Nagell–Lutz assembly, and **not** the project-specific denominator lemma (`den_no_simple_prime_factor_of_on_curve`, which lives in this project's `PIDDenominators`).

Note on the fork: the project context flagged that this might "already be in mathlib via the forked `DivisionPolynomial.*` / `EllipticDivisibilitySequence` files". Checked: those mathlib files contain only the **division-polynomial / EDS machinery** (definitions, degrees, leading coefficients), which the proof *consumes*. They do **not** contain any torsion-integrality or Nagell–Lutz statement. So this decl is genuinely new relative to mathlib — it is not a duplicated mathlib decl.

---

### Call sites — `x_isInteger_of_odd_prime_torsion_squarefree`

Internal use count: **1** (excluding the declaring file's own re-export region):
- `PIDPrimeOrder.lean:208` — inside `prime_order_integrality_squarefree` (same file): `have hx_int := x_isInteger_of_odd_prime_torsion_squarefree W hns hp hodd htors hsf`.

External-to-file callers: 0 distinct files (the one caller is in the same file). The downstream consumer of the *combined* result is `PIDMain.lean:98` (`prime_order_integrality_squarefree`), i.e. this theorem reaches `Main` only through its wrapper.

| Caller file:line | Usage pattern |
|------------------|---------------|
| PIDPrimeOrder.lean:208 | `x_isInteger_of_odd_prime_torsion_squarefree W hns hp hodd htors hsf` (feeds `prime_order_integrality_squarefree`) |

Inline-derivation grep: the **General track** has a structurally identical companion, `LutzNagell.PID`-vs-`General`: `x_integral_of_odd_prime_torsion_general` (`GeneralPrimeOrder.lean:80`), which proves the same statement specialized to `R = ℤ`, `K = ℚ` (concluding `∃ x₀ : ℤ, (x₀:ℚ) = x`). This is the project's intentional General/PID duplication (per the task brief), **not** a mathlib inline re-derivation. No mathlib-side re-derivation exists (mathlib has nothing in this area).

Call-sites signal: K = 1 internal use, single direct consumer (its own combined wrapper). This is a genuine proof-step lemma with a clear role, but it is **not** a broadly-reused API surface — it has exactly one consumer.

---

### Composition check (Phase 6)

Can `x_isInteger_of_odd_prime_torsion_squarefree` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1: `isInteger_of_root_squarefree_leading_coeff W … hψ hsf_lc` — but this is a **sibling project theorem** (`PIDPrimeOrder.lean:82`), not mathlib, and it in turn depends on `den_no_simple_prime_factor_of_on_curve` (project lemma in `PIDDenominators`). Not a mathlib composition.

Attempt 2: chain mathlib primitives directly. The proof needs, in sequence: (a) `evalEval_ψ_eq_zero_of_zsmul_eq_zero` (project lemma extracting `ψ_p(x,y)=0` from `p·P=0` via `zsmul_eq_smulEval`); (b) `evalEval_ψ_odd` + `WeierstrassCurve.map_preΨ` (mathlib) to turn it into `aeval x (W.preΨ p) = 0`; (c) `WeierstrassCurve.leadingCoeff_preΨ` (mathlib) to identify the leading coeff as `(p:R)`; (d) `den_dvd_of_is_root` (mathlib) + a **squarefree ⟹ no-repeated-prime denominator argument** that crucially uses the project's `den_no_simple_prime_factor_of_on_curve`. Step (d) is a real multi-step proof (the `by_contra` / `exists_irreducible_factor` / `q^2 ∤ den` reasoning in `isInteger_of_root_squarefree_leading_coeff`), **not** a 1-call composition, and it depends on a non-mathlib lemma.

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. It is a genuine multi-step assembly resting on at least one essential project-specific lemma (`den_no_simple_prime_factor_of_on_curve`) that is itself not in mathlib.

---

## Verdict: `LutzNagell.PID.x_isInteger_of_odd_prime_torsion_squarefree`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): Nagell–Lutz is a named theorem (BIG); the **integrality of torsion** is classical over ℤ and generalized over number fields — but **no** source states this exact intermediate with the bespoke "`(p:R)` squarefree" UFD hypothesis; the standard number-field proof uses formal groups/reduction, a different route.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (UFD-with-squarefree-`p` vs. Dedekind/number-field), but **not mechanically weakenable** — the general form is a different (EXPENSIVE) proof. Modern-idiom: none (already the typeclass-generalized form of the ℤ/ℚ theorem).
- Mathlib search (Phase 5): **not in mathlib**; mathlib has the rational-root + division-polynomial **building blocks** but no Nagell–Lutz / torsion-integrality result, and not the project's `den_no_simple_prime_factor` lemma.
- Composition check (Phase 6): **NOT-COMPOSABLE** in ≤3 mathlib calls; depends on an essential project-specific denominator lemma.

**Rationale:**

This is a real, non-trivial intermediate step of the **Nagell–Lutz theorem** — a flagship named result that mathlib does **not** yet have in any form (mathlib's elliptic-curve tree has the division-polynomial machinery this proof consumes, but no torsion-integrality statement whatsoever). So it is neither already-in-mathlib (rules out NO-mathlib-has-it) nor a ≤3-call composition of mathlib primitives (rules out NO-composable: the core "squarefree ⟹ denominator is a unit on the curve" step is a genuine multi-line proof resting on the project's own `den_no_simple_prime_factor_of_on_curve`).

It is **not** a clean YES either. The "`(p:R)` squarefree" hypothesis is a **bespoke packaging** found in no standard reference; the statement is one specific intermediate (odd-prime order, x-coordinate only) of a larger theorem, with exactly **one internal consumer** and a duplicated General-track sibling. Mathlib's iron rule is to add the *right* statement at the *right* generality. The right mathlib artifact in this area is almost certainly a **clean Nagell–Lutz theorem** (over ℤ, and/or over a Dedekind domain via the standard reduction/formal-group route) — and whether mathlib wants *this particular UFD-squarefree intermediate exported as a named lemma*, versus only the final assembled theorem (with intermediates kept private), is a **mathlib-taste + project-policy judgment** the skill should not make alone. The whole Nagell–Lutz formalization is the natural upstreaming unit; this single step's fate is decided by how that upstreaming is structured.

**BORDERLINE — numbered questions for the human:**
1. Is the intended mathlib contribution the **whole Nagell–Lutz theorem** (assembled final statement), with steps like this one kept `private`/internal? If yes → this decl is NO-as-a-standalone (folded into the PR, not exported). yes/no
2. Should the upstreamed statement target **ℤ** (the classical Nagell–Lutz, matching every textbook) and/or a **Dedekind domain / `𝒪_K`** (the literature generalization, via formal groups/reduction) — rather than the current "UFD + squarefree `p`" framing? yes/no
3. Is the "`(p:R)` squarefree" hypothesis intended as a permanent part of the public API, or only a stepping stone toward the unconditional (formal-group-based) torsion-integrality result? (permanent / stepping-stone)
4. Given the General/PID duplication (`x_integral_of_odd_prime_torsion_general` over ℤ/ℚ vs. this UFD version), should only **one** of the two be upstreamed, with the other deleted as project scaffolding? yes/no
5. Is upstreaming Nagell–Lutz to mathlib a current goal at all, or is this project's formalization intended to live in AINTLIB? (mathlib-target / AINTLIB-resident)

**Next action:** user answers the questions; re-run `/mathlibable LutzNagell.PID.x_isInteger_of_odd_prime_torsion_squarefree` to resolve. Most likely resolutions: if (1)=yes or (5)=AINTLIB-resident → effectively NO-as-standalone (keep internal, upstream the assembled Nagell–Lutz theorem when ready); if the project commits to exporting the UFD-squarefree intermediate as public API → YES-but-generalise-first toward the Dedekind/number-field statement (EXPENSIVE, new proof).

---

## Next step

Answer the five numbered questions above, then re-run `/mathlibable` on this decl. The verdict turns entirely on the upstreaming policy for the Nagell–Lutz formalization (whole-theorem PR with private steps vs. exporting this intermediate) and the target base ring (ℤ / Dedekind vs. the current UFD-squarefree framing) — a judgment call left to the maintainer.
