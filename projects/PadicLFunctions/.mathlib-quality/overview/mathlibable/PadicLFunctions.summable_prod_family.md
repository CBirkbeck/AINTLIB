# `/mathlibable` report — `PadicLFunctions.summable_prod_family`

**Final verdict: `BORDERLINE-needs-human`**

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task note); **reasoned from source** — declaration + all dependencies (`InExpBall`, `coeff`/`PowerSeries.coeff`, `master_bridge`, `norm_coeff_pow_le`, `coeff_pow_eq_zero_of_lt`, `pow_norm_sum_le`) read directly.
- decl `PadicLFunctions.summable_prod_family`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:760`
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp`/`log` convergence on the nonarchimedean ball `‖x‖ < p^{−1/(p−1)}` of a complete ultrametric `ℚ_[p]`-algebra field, and that they invert each other on matched balls (Washington §5.1, Cassels §12).

---

### Statement (Phase 1)

`summable_prod_family` is a **theorem** stating the following:

Let `ℚ_[p]` be the `p`-adic numbers and `L` a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra. Let `F, G ∈ ℚ_[p]⟦X⟧` be formal power series and `y ∈ L` a point in the open convergence ball of the `p`-adic exponential (`‖y‖^{p−1} < p⁻¹`, written `InExpBall p y`). Assume `F` and `G` both satisfy the **Legendre coefficient bound** `‖[Xʲ]·‖^{p−1} ≤ p^{j−1}` for every `j ≥ 1`, and that `G` has zero constant term. Then the doubly-indexed family over `ℕ × ℕ`

  `(n, k) ↦ ([Xⁿ]F · [Xᵏ](Gⁿ)) · yᵏ`

is **summable** in `L`. (This is exactly the summability hypothesis that the evaluation bridge `master_bridge` needs in order to interchange the order of summation by ultrametric Fubini when composing `F` with `G` and evaluating at `y`.)

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete nonarchimedean `ℚ_[p]`-algebra field (the coefficient field for evaluation).
- `F G : PowerSeries ℚ_[p]` — the outer and inner formal power series of the composition `F.subst G`.
- `y : L` — the evaluation point.

Hypotheses (Lean side):
- `hy : InExpBall p y` — i.e. `‖y‖^{p−1} < p⁻¹`; gives the geometric decay ratio `ρ := p·‖y‖^{p−1} < 1` driving the tail estimate.
- `hF : ∀ n, 1 ≤ n → ‖[Xⁿ]F‖^{p−1} ≤ p^{n−1}` — Legendre bound on the outer series' coefficients.
- `hGc : ∀ j, 1 ≤ j → ‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` — Legendre bound on the inner series' coefficients.
- `hG0 : constantCoeff G = 0` — `G` has no constant term (so `[Xᵏ](Gⁿ) = 0` for `k < n`, giving the support condition `n ≤ k`).

Conclusion (math): the product family `((n,k) ↦ [Xⁿ]F·[Xᵏ](Gⁿ)·yᵏ)` is summable over `ℕ × ℕ`.

Conclusion (Lean): `Summable fun nk : ℕ × ℕ => ((coeff nk.1 F : ℚ_[p]) * (coeff nk.2 (G ^ nk.1) : ℚ_[p])) • y ^ nk.2`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a proof-internal summability helper (decomposition cluster R5.E), not a `## Main results` entry, not named after a person/place. Its sole purpose is to discharge the `hprod` hypothesis of `master_bridge`; it feeds exactly two call sites and is invisible outside this file.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: ~57 substantive lines (a real analytic proof: cofinite-zero reduction, geometric-tail majorant, support-condition `n ≤ k`, case split on `x.1 = 0`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (and the body is far from one line regardless).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential logarithm composition formal power series double sum summability convergence" | partial | nonarchimedean series converges ⟺ terms → 0; exp converges on `‖x‖ < p^{−1/(p−1)}` | Wikipedia *p-adic exponential function*; MIT/UChicago/Conrad REU notes. The convergence *criterion* is standard; no named "product-family summability" lemma surfaced. |
| 2 | WebSearch (general form) | "summability double family formal power series substitution nonarchimedean field Fubini coefficient bound" | no | (archimedean Gevrey/k-summability papers only) | The "summable family of formal series" notion that appeared is unrelated (Borel/multisummability), not the nonarchimedean double-sum-over-`ℕ×ℕ` statement here. |
| 3 | WebSearch (named-after / aliases) | "exp log inverse p-adic proof Fubini interchange order of summation power series composition Washington cyclotomic" | partial | exp/log inversion is classical (Washington §5.1, Cassels §12, Cohen §4.4); proof interchanges the double sum | Confirms the *technique* is standard and textbook; the interchange is justified by "terms → 0", **not** isolated as a named lemma. |
| 4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of the double-family summability in p-adic exp/log composition") | n/a | — | ChatGPT MCP server not configured in this environment (`/setup-chatgpt` not run). Recorded n/a per protocol. |
| 5 | Local references | grep `.mathlib-quality/references/` + repo `refs/PadicLFunctions/` for the concept | n/a | (no references dir) | `.mathlib-quality/references/` absent; `refs/` absent. Recorded n/a. The decomposition (`PadicExp.lean` docstring) cites RJW Lem 5.14, Cassels §12, Washington §5.1 as the math sources. |
| 6 | nLab | "p-adic exponential logarithm formal power series convergence" (site:ncatlab.org) | partial | nLab *power series*: formal `exp`/`log` for zero-constant-term elements; *geometric series* | nLab has the formal-series exp/log and the convergence-in-suitable-topology remark, but **no** dedicated p-adic-composition-summability statement. `p-adic+exponential+map` page is 404 (does not exist). |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept (a concrete normed-field summability estimate). |
| 8 | Stacks Project | — | n/a | — | Not an algebraic-geometry concept (no schemes/sheaves; pure p-adic analysis). |
| 9 | MathOverflow / Math.SE | covered by #1/#3 generality sweeps (p-adic exp/log inversion proof, interchange of summation) | partial | same as #3 — the interchange is a routine textbook step | No MO/SE thread elevates the double-family summability to a citable standalone result. |
| 10 | recent arXiv (≤5 yr) | "summability ... nonarchimedean field Fubini coefficient bound" (arXiv hits in #2) + "p-adic exponential logarithm formal power series" (#6) | no | (arXiv hits are archimedean summability or unrelated p-adic topics) | e.g. arXiv:1603.00689, 0804.3049, 0705.4047 — none state this lemma. |

### Literature summary (Phase 3)

Concept identified as: **summability of the double-indexed "product family" arising when composing two `p`-adic formal power series and evaluating in the convergence ball** — i.e. the Fubini-justification step inside the proof that the `p`-adic `exp` and `log` are mutually inverse.

Sources agree on the standard form: **no — there is no standard *named* form.** What the literature agrees on is the *ingredient*: in a nonarchimedean complete field a family is summable iff its terms tend to zero (along the cofinite filter), and exp/log inversion is proved by interchanging a double sum. The double-family summability is a **proof step**, not a named theorem; references (Washington §5.1, Cassels §12, Cohen §4.4) carry out the interchange inline.

Most general standard form: the only "general object" near this is mathlib's **formal** substitution-summability (`PowerSeries.summable_subst` / `subst_tsum`) — summability of `i ↦ (x i).subst a` for a summable `x` in a topological ring. That is the *formal*-algebra statement; the present lemma is the *analytic/normed* counterpart specialised to `ℚ_[p]`-coefficients with explicit Legendre norm bounds and the `InExpBall` decay ratio.

Generality dimensions where the literature varies:
- **Coefficient field**: literature does `ℂ_p` / extensions of `ℚ_p`; here `L` = any complete ultrametric `ℚ_[p]`-algebra field (already fairly general).
- **Decay hypothesis encoding**: literature uses valuations / `|·| < r`; here the bespoke rpow-free encoding `‖·‖^{p−1} ≤ p^{j−1}` and `‖y‖^{p−1} < p⁻¹` (project convention, matches its sibling Legendre lemmas).
- **What is being summed**: literature keeps it implicit inside the proof; the project pulls it out as a reusable `Summable (ℕ × ℕ → L)` statement so two inversion proofs can share it.

Because the protocol returned **no named standard form** — only the ambient classical technique — this is itself a signal: the declaration is a proof-internal bookkeeping lemma, which pushes Phase 7 toward BORDERLINE / NO rather than a clean YES.

---

### Generality analysis — `PadicLFunctions.summable_prod_family`

Literature-standard form (from Phase 3): there is no named literature form; the nearest *general* anchor is the formal-substitution-summability idiom (mathlib `summable_subst`) re-cast analytically for normed coefficients.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] … [IsUltrametricDist L] [CompleteSpace L]` over `ℚ_[p]` | complete ultrametric `ℚ_[p]`-algebra field | complete nonarchimedean extension of `ℚ_p` | partly | Ultrametricity + completeness are genuinely used (the cofinite-zero summability criterion `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` and the ultrametric sum bound `pow_norm_sum_le`). Could in principle drop `Field → DivisionRing/Algebra`, but the coefficient ring being `ℚ_[p]` is baked into the Legendre bounds — not a free generalisation. |
| 2 | `hF`, `hGc` : `‖[Xʲ]·‖^{p−1} ≤ p^{j−1}` | rpow-free `p`-adic Legendre bounds | abstract "Gauss-norm / radius-of-convergence" condition | yes (idiom) | The `^{p−1}`/`p^{j−1}` encoding is a **project convenience** (avoids `Real.rpow`). A mathlib-idiomatic form would phrase the hypothesis as a Gauss-norm / convergence-radius bound (cf. the sibling lemma `norm_coeff_pow_le`, whose modern target is `PowerSeries.gaussNorm_pow_le`). This is a real reformulation axis, not a free weakening. |
| 3 | `hy : InExpBall p y` (`‖y‖^{p−1} < p⁻¹`) | the exp-ball decay condition | "`y` inside the radius of convergence of the composite" | yes (idiom) | Same rpow-free encoding issue; the genuine content is "the geometric ratio `p·‖y‖^{p−1} < 1`". A general statement would take the ratio bound directly, decoupled from `exp`. |
| 4 | `hG0 : constantCoeff G = 0` | inner series has zero constant term | order(`G`) ≥ 1 (substitution well-defined) | NO | Essential and standard — this is exactly mathlib's `HasSubst` precondition; gives the support condition `n ≤ k`. Cannot be dropped. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (in the same sense as its sibling `norm_coeff_pow_le`): the rpow-free `ℚ_[p]`-specific Legendre/`InExpBall` encoding is a deliberate project specialisation of a more idiomatic Gauss-norm / radius-of-convergence statement, and the whole lemma is the *analytic* shadow of mathlib's *formal* `summable_subst`.

Number of weakening/reformulation opportunities found: **3** (rows 1–3 above; row 4 is essential).

Proposed restatement (if STRICTLY NARROWER): the honest general target is a **normed-coefficient substitution-summability lemma** — "if the inner series `G` (order ≥ 1) and the outer series `F` have coefficient norms within a common geometric radius, and `y` lies strictly inside the composite radius of convergence, then the product family `(n,k) ↦ [Xⁿ]F·[Xᵏ](Gⁿ)·yᵏ` is summable" — stated with a Gauss-norm / convergence-radius hypothesis rather than the rpow-free `p^{j−1}` encoding, in a complete nonarchimedean normed algebra. This would be the analytic companion to mathlib's formal `PowerSeries.summable_subst`.

Cost of restatement: **EXPENSIVE** — the current proof is wired end-to-end to the explicit `‖·‖^{p−1} ≤ p^{j−1}` bounds and the `p·‖y‖^{p−1} < 1` ratio (every `calc` step uses the integer power `p−1`); re-proving against an abstract Gauss-norm radius needs genuinely new estimates, not a mechanical rewrite.

(Cost note: EXPENSIVE does not by itself downgrade the bucket. But — see Phase 7 — combined with "is the abstract analytic-substitution lemma the right mathlib target at all, when no p-adic exp/log exists upstream to consume it" this becomes a human judgment, not a self-resolving downgrade.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already fully typeclass-driven (`NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`) | — |
| 2 | sequences/metric → filters/topological? | **partly** | the proof already uses the cofinite filter (`summable_iff_tendsto_cofinite_zero`); the *statement* is `Summable`, which is filter-based. No further filter-isation gain. | already filter-native |
| 3 | construct an object → universal-property class? | no | it is a summability proposition, nothing to characterise universally | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | no substructure here | — |
| 5 | vector-space/metric/field-specific → weaken typeclasses (modules / pseudometric / semiring)? | **yes** | re-state coefficient bounds via a **Gauss-norm / radius-of-convergence** condition in a complete nonarchimedean normed algebra (drop the bespoke rpow-free `p^{j−1}` encoding) | composes with mathlib's `PowerSeries.summable_subst` / `subst_tsum` and a (currently-missing) `gaussNorm` convergence API; unifies with the sibling `gaussNorm_pow_le` modernisation flagged for `norm_coeff_pow_le` |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index (ℕ,ℤ,ℝ) → general additive/ordered structure? | no | the `ℕ × ℕ` index is intrinsic (power-series degrees); already general | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (rows 5, and partially via the Gauss-norm route shared with the sibling lemma)**.
- Proposed mathlib-idiomatic restatement: an analytic substitution-summability lemma over a complete nonarchimedean normed `ℚ_[p]`-algebra, with the coefficient/decay hypotheses phrased through `PowerSeries.gaussNorm` (radius of convergence) rather than the rpow-free `‖·‖^{p−1} ≤ p^{j−1}` encoding, packaged as the *analytic* companion of mathlib's *formal* `summable_subst`.
- Cost: **EXPENSIVE** (the proof's estimates are written against the integer `(p−1)`-power encoding throughout).
- Mathlib downstream this enables: would slot beside `PowerSeries.summable_subst` and a `gaussNorm`-based convergence API; would be the genuine reusable object (a *general* analytic-substitution-summability lemma) rather than a `p`-adic-exp/log-specific bookkeeping step.
- Real mathematical improvement (not just "looks cooler"): **plausible but unproven** — the modern form would be reusable for *any* nonarchimedean power-series composition, not just exp/log. **But** mathlib currently has **no** p-adic `exp`/`log` and no analytic-substitution-convergence layer at all, so the modern form has **no existing consumer upstream**; whether mathlib wants to open that layer with this lemma as the seed is exactly the human call (Phase 7).

Because Phase 4b is STRICTLY NARROWER **and** Phase 4c finds a real modern-idiom target, the YES path — *if taken* — would be `YES-but-generalise-first`, never `YES-add-as-is`. But the "is the general analytic-substitution layer the right thing to add to mathlib at all, with no upstream consumer and an EXPENSIVE regeneralisation" question is what makes the whole thing BORDERLINE rather than a self-resolving YES (see Phase 7).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.summable_prod_family`

[A] Lean-Finder — n/a: the hosted Lean-Finder service is not reachable from this environment. Substituted with an exhaustive local grep of the pinned mathlib (`.lake/packages/mathlib`) — see [D]/[E].
[B] Loogle — type-pattern target `Summable (fun _ : ℕ × ℕ => (_ * _) • _ ^ _)` and `Summable (?f : ℕ × ℕ → ?L)` with `HasSubst`/`coeff` constraints — n/a (service not reachable here); covered by the local source grep below.
[C] LeanSearch — natural-language "summability of the product family of a power series substitution / evaluation, p-adic exp log composition" — n/a (service not reachable here); the literature/NL angle is covered by Phase 3.
[D] **Grep mathlib src** — terms tried: `Summable fun.*ℕ × ℕ`, `summable.*subst`, `coeff.*subst.*Summable`, `PowerSeries.subst`/`HasSubst`, `padicExp`/`p-adic exponential`/`p-adic logarithm`, `Summable.const_smul`/`smul_const`, `summable_prod_of_nonneg`, `Summable.mul_of_nonneg`/`mul_norm`, `summable_iff_tendsto_cofinite_zero`. **Findings:** mathlib's substitution-summability is **formal only** — `PowerSeries.summable_subst` / `subst_tsum` (Mathlib/RingTheory/PowerSeries/Substitution.lean:599,604): "if `x` is summable then `i ↦ (x i).subst a` is summable" in a *topological ring* — not the concrete `ℚ_[p]`-normed double-family statement here. Mathlib has **no p-adic `exp`/`log`** (all `Exponential*.lean` files are C*-algebra/complex/matrix/quaternion — archimedean). The genuine building blocks exist: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, `Summable.const_smul`/`Summable.smul_const`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Summable.of_norm_bounded(_eventually)`, `summable_prod_of_nonneg` — but no packaged form.
[E] **Name pattern** — `summable_prod_family`, `summable_prod`, `prod_family` across mathlib: **no hits** (the only `summable_prod*` are `summable_prod_of_nonneg` for ℝ-valued families and `Summable.prod_factor`, both unrelated).

Searched for both:
  - the user's current form (rpow-free `ℚ_[p]` Legendre/`InExpBall` family) — **not in mathlib**;
  - the literature-standard / modern-idiom form (analytic substitution-summability via Gauss-norm in a nonarchimedean algebra) — **also not in mathlib** (only the *formal* `summable_subst` exists).

Concluded: **"not in mathlib"** — all reachable methods exhausted (local mathlib grep substituting for the unreachable hosted search services), under both the current form and the more-general analytic-substitution form. Mathlib has the *building blocks* and the *formal* substitution-summability, but neither the exact statement nor a more-general analytic version we would specialise from.

---

### Call sites — `PadicLFunctions.summable_prod_family`

Internal use count: **2** (within the project, NOT counting the declaring line `:760`)
External-to-file callers: **0** distinct files (whole-repo grep over `projects/**/*.lean` returns only `PadicExp.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:943 | `summable_prod_family p (exp ℚ_[p]) (PowerSeries.log ℚ_[p]) (x - 1) hx (norm_coeff_exp_le p) (norm_coeff_log_le p) constantCoeff_log` — passed as the `hprod` argument of `master_bridge` inside `padicExp_padicLog` (exp ∘ log = id). |
| PadicExp.lean:967 | `summable_prod_family p (PowerSeries.log ℚ_[p]) (exp ℚ_[p] - 1) x hx (norm_coeff_log_le p) hGc hG0` — passed as the `hprod` argument of `master_bridge` inside `padicLog_padicExp` (log ∘ exp = id). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `summable_prod_family`?): **(none)** — the only summability-over-`ℕ×ℕ` of this product family in the project is this lemma; both consumers route through it.

**What the pattern tells us:** K = 2 internal uses, no inline re-derivation, **0 external** — both uses feed the *same* downstream consumer (`master_bridge`), and that consumer is itself only used by the two inversion theorems. This is a genuine but **shallow** API: it factors a shared step out of two sibling proofs in one file. Per the Phase-6 signal table this is between "K = 1 (wrong abstraction)" and "K ≥ 3 (real API)" — it leans away from a clean YES, and reinforces the project-internal-helper reading.

### Composition check (Phase 6)

Can `summable_prod_family` be derived from mathlib in ≤3 chained calls?

Attempt 1: `PowerSeries.summable_subst` (the formal substitution-summability) ∘ a coefficient-extraction map.
  - Mathlib decls used: `PowerSeries.summable_subst`, `Summable.smul_const`/`const_smul`.
  - Result: **fails** — `summable_subst` lives in the *formal*/topological-ring world (summability of a family *of power series*); it does not produce summability of the *scalar* family `(n,k) ↦ [Xⁿ]F·[Xᵏ](Gⁿ)·yᵏ` in the normed field `L`. There is no 1–3 call bridge between them; the gap is the whole analytic estimate.

Attempt 2: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` + a geometric majorant (`Summable.of_norm_bounded_eventually` + `tendsto_pow_atTop_nhds_zero_of_lt_one`).
  - Mathlib decls used: `summable_iff_tendsto_cofinite_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `pow_norm_sum_le` (itself a project lemma), `norm_coeff_pow_le` (project), `coeff_pow_eq_zero_of_lt` (project).
  - Result: **fails as a composition** — this *is* the proof, and it is ~57 lines: reduce to cofinite-zero, build the explicit geometric tail majorant `p⁻¹·(p‖y‖^{p−1})ᵏ`, prove it `< ε^{p−1}` past some `K`, then a case split (`x.1 = 0`) plus the support argument `x.1 ≤ x.2` from `coeff_pow_eq_zero_of_lt`. It uses two *project* helpers (`norm_coeff_pow_le`, `pow_norm_sum_le`) that are themselves non-mathlib, and real `calc`/`omega`/`field_simp` reasoning — not a chain of ≤3 mathlib calls.

Conclusion: **NOT-COMPOSABLE.** Mathlib supplies the ingredients (cofinite-zero criterion, geometric decay, norm-bounded summability) but assembling them into this statement is a genuine multi-step analytic proof, not a 1–3 call composition. (This rules out `NO-composable-from-mathlib`.)

---

## Verdict: `PadicLFunctions.summable_prod_family`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): exp/log inversion is classical (Washington §5.1, Cassels §12, Cohen §4.4) and the double-sum interchange is a routine textbook step justified by the nonarchimedean "terms → 0" criterion — but there is **no named standalone result** for "the product family of an evaluation bridge is summable". 9-channel sweep ran (ChatGPT MCP n/a — unconfigured; local refs n/a — absent); no standard form found.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the rpow-free `‖·‖^{p−1} ≤ p^{j−1}` / `InExpBall` encoding is a deliberate `ℚ_[p]`-specialisation; the idiomatic target (Phase 4c, row 5) is an analytic substitution-summability lemma phrased via `gaussNorm`/convergence-radius, companion to mathlib's *formal* `summable_subst`. Regeneralisation cost: **EXPENSIVE**.
- Mathlib search (Phase 5): **not in mathlib** under either form. Mathlib has the *formal* `PowerSeries.summable_subst`, the nonarchimedean cofinite-zero criterion, and geometric-decay/norm-bounded-summability lemmas, but no p-adic `exp`/`log` and no analytic-substitution-convergence layer for this to attach to or specialise from.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a ~57-line analytic proof leaning on two further *project* helpers; not ≤3 mathlib calls). Call sites: **K = 2**, both internal, both feeding `master_bridge`; **0** external; no inline re-derivation.

**Rationale (why BORDERLINE, not a self-resolving bucket):**

Every individual phase is clean, and they jointly rule out three of the five buckets: it is genuinely **not in mathlib** (kills `NO-mathlib-has-it`), it is **not a ≤3-call composition** (kills `NO-composable-from-mathlib`), and because Phase 4b is STRICTLY NARROWER and Phase 4c finds a real modernisation target, it is **not** `YES-add-as-is`. What remains is the choice between `YES-but-generalise-first` (target = the analytic-substitution-summability lemma via `gaussNorm`) and "keep it project-local / drop from mathlib consideration" — and that choice rests on three judgments the skill cannot ground in the evidence alone:

(1) **No upstream consumer exists.** Mathlib has no p-adic `exp`/`log` and no analytic power-series-substitution-convergence layer. The *general* form Phase 4c proposes would be the seed of a brand-new layer with **zero current mathlib clients** — its only demonstrated consumers are this project's two inversion proofs (via `master_bridge`). Whether mathlib wants to open that analytic-substitution layer *now*, with this lemma as the seed, is a library-direction/taste call. (2) **Form + cost tension.** The reusable object is the abstract analytic-substitution lemma, not this rpow-free `ℚ_[p]` bookkeeping statement; re-proving in the abstract form is EXPENSIVE (new estimates, not a rewrite), and the abstract form itself depends on first landing a `gaussNorm` convergence API — i.e. this is a *multi-PR programme*, not a single upstream-this-lemma action. (3) **Consistency with the sibling assessment.** This lemma's immediate feeder, `norm_coeff_pow_le`, was assessed `BORDERLINE-needs-human` for the *same* shape (rpow-free `p`-adic corollary vs. a general `gaussNorm`-based mathlib target, single internal consumer). `summable_prod_family` sits one level up the same cluster (R5.E) and inherits the same open question — resolving it requires the user's decision on whether to pursue the general analytic-substitution layer at all. This is a genuine *form + scope* ambiguity, **not** a cost-based downgrade.

**Numbered questions (≤5):**

1. Do you want mathlib to gain a **general analytic power-series-substitution-summability** lemma — "for `F, G` (ord `G ≥ 1`) over a complete nonarchimedean normed algebra, with coefficient norms inside a common radius and `y` strictly inside the composite radius of convergence, the family `(n,k) ↦ [Xⁿ]F·[Xᵏ](Gⁿ)·yᵏ` is summable" — as the *analytic companion* to the existing formal `PowerSeries.summable_subst`? If **yes**, this is `YES-but-generalise-first` with that as the target (EXPENSIVE; likely depends on first landing a `gaussNorm`/convergence-radius API — see Q2/Q3). If **no**, keep `summable_prod_family` project-local as the bespoke `hprod`-provider for `master_bridge`.

2. Is the existing `norm_coeff_pow_le` / `gaussNorm_pow_le` decision (its sibling report) already settled? The general substitution-summability lemma in Q1 should be phrased through the **same** Gauss-norm / radius-of-convergence vocabulary; pursuing this lemma only makes sense once that hypothesis idiom is agreed.

3. Are you willing to treat this as a **multi-PR programme** (Gauss-norm convergence API → analytic-substitution-summability → p-adic exp/log built on top), rather than upstreaming this single lemma? The lemma in isolation has no mathlib consumer; it only earns its place if the surrounding analytic-substitution layer is also planned.

4. If the answers to Q1–Q3 are "not now / keep local", do you agree the right action is to leave `summable_prod_family` in `PadicExp.lean` as a project-internal helper (it is sorry-free, used twice, correctly factored) and **drop it from mathlib consideration**?

**Next action:** user answers the questions. If Q1 = yes (and Q2/Q3 align), hand off to `/generalise PadicLFunctions.summable_prod_family` with the analytic-substitution-summability lemma (Gauss-norm hypotheses, companion to `PowerSeries.summable_subst`) as the explicit target, sequenced after the `gaussNorm` convergence API. If Q1 = no, keep it project-local and remove it from the mathlibable queue. Then re-run `/mathlibable PadicLFunctions.summable_prod_family` only if the scope decision changes.

---

## Next step

User answers questions 1–4. Likely resolution (mirroring the sibling `norm_coeff_pow_le` outcome): pursue the **general** analytic substitution-summability lemma upstream as part of a `gaussNorm`-convergence programme (`YES-but-generalise-first` on the *general* form), while keeping this rpow-free `ℚ_[p]`-specific statement project-local as the `hprod` engine for `master_bridge`.
