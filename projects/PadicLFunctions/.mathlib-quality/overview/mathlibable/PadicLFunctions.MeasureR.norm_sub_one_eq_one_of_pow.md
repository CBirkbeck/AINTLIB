# `/mathlibable` report — `PadicLFunctions.MeasureR.norm_sub_one_eq_one_of_pow`

> **Final verdict: `BORDERLINE-needs-human`** (most likely resolution: `YES-but-generalise-first` — generalise from a `ℚ_[p]`-algebra normed field to a general ultrametric normed (comm) ring before any mathlib PR).

Mode A, full 10-phase workflow. The exhaustive 9-channel literature search ran; the ChatGPT MCP channel is unavailable in this environment and is recorded `n/a` with reason.

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task note); reasoned from source — Phase-0 fallback.
- decl `PadicLFunctions.MeasureR.norm_sub_one_eq_one_of_pow`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:78`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6) — distribution-free route via the explicit antiderivative `F̃_θ`.

Ambient context at the declaration (file lines 39–42, with line-72 `omit`):
```lean
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
omit [CompleteSpace K] [CharZero K] in   -- ← drops Complete/CharZero for this lemma
```
So the lemma's *effective* typeclass surface is `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]`, with a prime `p` floating in scope. `p`, the `NormedAlgebra ℚ_[p] K` instance, and `NormedField` (vs. `NormedRing`) are **never used in the proof** — see Phase 4.

---

### Statement (Phase 1)

`norm_sub_one_eq_one_of_pow` states the following:

> Let `K` be a non-archimedean (ultrametric) normed field and `x ∈ K` with `‖x‖ ≤ 1`. If some power satisfies `‖xᵐ − 1‖ = 1`, then `‖x − 1‖ = 1`.

It is a one-step **lifting lemma**: norm-one of `x − 1` is recovered from norm-one of `xᵐ − 1` (together with `x` lying in the closed unit ball). Mathematically it is a packaging of two textbook ultrametric facts:
1. the ultrametric (strong-triangle / isosceles) bound `‖x − 1‖ = ‖x + (−1)‖ ≤ max(‖x‖, 1) = 1`;
2. the factorisation `xᵐ − 1 = (Σ_{i<m} xⁱ)·(x − 1)`, where the geometric factor has norm `≤ 1` (each `‖xⁱ‖ ≤ 1`), so `1 = ‖xᵐ − 1‖ ≤ ‖x − 1‖`.
Antisymmetry of `≤` closes it.

Variables / typeclasses (Lean side):
- `K` — the coefficient field; the proof needs only an ultrametric normed (comm) ring structure.
- `x : K` — the element; `m : ℕ` — the exponent.

Hypotheses (Lean side):
- `hpow : ‖x ^ m - 1‖ = 1` — the power is at the boundary of the unit ball.
- `hx : ‖x‖ ≤ 1` — `x` is in the closed unit ball.

Conclusion (math): `‖x − 1‖ = 1`.
Conclusion (Lean): `‖x - 1‖ = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a private-style helper lemma (general ultrametric utility), not a `def`/`class`/`structure`, not a `## Main results` entry, not named after a person/place. Its docstring marks it "P6-p9 helper".

(Literature width is EXHAUSTIVE regardless; BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines (a `calc`, a geometric-sum norm bound, a split inequality, `le_antisymm`).
One-liner verdict: **n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`.** Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "ultrametric field norm of x−1 equals one when norm of xᵐ−1 equals one"                                | partial | the two ingredient facts, not the combined implication | Kedlaya p-adic notes; Wolfram MathWorld; Cambridge excerpt — confirms ultrametric `‖x+y‖≤max`, residue-class characterisation of `‖x−y‖=1`. No named combined lemma. |
|  2 | WebSearch (general form / mechanism) | non-archimedean abs value, root of unity, `xᵐ−1 = (x−1)(1+x+…+xᵐ⁻¹)`, cyclotomic factor                | partial | factorisation + norm-one of roots of unity standard | Bouyer *Local Fields* notes; arXiv non-archimedean function theory. Confirms each ingredient is textbook; the packaged one-liner is not a named result. |
|  3 | WebSearch (mechanism / lift)     | "p-adic valuation |x−1|=1 from |xⁿ−1|=1 and |x|≤1 ultrametric inequality lift"                          | partial | isosceles principle: `|x|≠|y| ⇒ |x+y|=max` | UH topological-groups notes; UChicago Quick REU; Wikipedia p-adic valuation. The "lift" is folklore, not a citable theorem. |
|  4 | ChatGPT MCP                      | "standard form / generality / historical evolution of: `‖x−1‖=1` from `‖xᵐ−1‖=1`, `‖x‖≤1`, ultrametric" | **n/a** | — | **ChatGPT MCP server not installed in this environment** (`/setup-chatgpt` not run; no `mcp__*chatgpt*`/`openai` tool surfaced). Recorded n/a per protocol. The three WebSearch queries already cover specific/general/named-alias generality levels. |
|  5 | Local references                 | `.mathlib-quality/references/` for "ultrametric", "norm", "root of unity"                              | n/a  | (no references dir on this branch) | `projects/PadicLFunctions/.mathlib-quality/references/` absent in this worktree — recorded n/a. |
|  6 | nLab                             | non-archimedean valuation / ultrametric isosceles triangle                                             | yes  | `|x|≠|y| ⇒ |x+y|=max(|x|,|y|)`; "all triangles isosceles" | planetmath "ultrametric triangle inequality"; IAS *Geometry in which all triangles are isosceles*. Underpins ingredient (1). |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not a categorical concept          | A norm inequality in a normed ring; no categorical structure to look up. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept  | Elementary p-adic/ultrametric analysis; not in Stacks' scope. |
|  9 | MathOverflow / Math.StackExchange| `|x−1|=1` from `|xⁿ−1|=1`, ultrametric, `x` in unit ball                                                 | partial | folklore exercise; no canonical reference | Discussed as a standard p-adic exercise; no "named" theorem. |
| 10 | recent arXiv (last 5 years)      | non-archimedean dynamics / roots of unity on Laurent series                                            | partial | ingredient facts reused freely as "standard" | arXiv:2512.00982, arXiv:1111.1993 etc. treat the ingredients as assumed background, never isolating this implication. |

### Literature summary (Phase 3)

Concept identified as: **ultrametric "norm-one lifting from a power"** — a corollary of (a) the strong-triangle / isosceles inequality and (b) the `geom_sum_mul` factorisation of `xᵐ − 1`.
Sources agree on the standard form: **yes for the two ingredients; no canonical name for the combined implication.** Every p-adic / non-archimedean reference treats both ingredients as textbook background and uses them inline; none packages this exact "from `‖xᵐ−1‖=1` and `‖x‖≤1` get `‖x−1‖=1`" step as a stated lemma.
Most general standard form: holds in **any ultrametric normed (commutative) ring** — no field, no `ℚ_[p]`-algebra, and no prime `p` are needed. The ingredients are the ring-level `geom_sum_mul` and the ultrametric `norm_add_le_max` / `norm_sum_le_…` API.
Generality dimensions where the literature varies:
  - coefficient structure: literature uses it freely over any non-archimedean **field**, but the proof only needs a normed **ring** with `IsUltrametricDist`. The most general is the ring.
Disagreement with the literature: **none** — the user's statement is a faithful, slightly-over-specialised instance of the folklore fact.

If the protocol had returned literally nothing this would suggest an over-narrow concept; here it returned the *ingredients* (standard) but not a *named combined lemma*, which is the signature of a small but legitimate utility lemma — exactly the kind whose mathlib-worthiness is a taste call.

---

### Generality analysis — `norm_sub_one_eq_one_of_pow`

Literature-standard form (from Phase 3): the implication over any ultrametric normed (commutative) ring.

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]`                 | non-archimedean normed **field**   | ultrametric normed **(comm) ring** | **yes**            | Proof uses only `geom_sum_mul`, `norm_pow`, `norm_mul`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `pow_le_one₀`, `mul_le_of_le_one_left` — all available in a (semi/comm) `NormedRing` with `IsUltrametricDist`. No inverse / field structure is used. |
| 2 | `[NormedAlgebra ℚ_[p] K]`         | `ℚ_[p]`-algebra                    | — (irrelevant)                   | **yes (drop entirely)** | Never referenced in the proof; pure ambient noise inherited from the `variable` block. |
| 3 | `(p : ℕ) [Fact p.Prime]`          | a fixed prime in scope             | — (irrelevant)                   | **yes (drop entirely)** | `p` does not appear in the statement or proof. |
| 4 | `[IsUltrametricDist K]`           | ultrametric                        | ultrametric                      | NO                  | Load-bearing: `norm_add_le_max` and `norm_sum_le_of_forall_le_of_nonneg` are exactly the ultrametric API. Cannot weaken. |
| 5 | `(hx : ‖x‖ ≤ 1)`, `(hpow : ‖xᵐ−1‖=1)` | the two hypotheses             | same                             | NO                  | Both essential (`hx` bounds the geometric factor; `hpow` provides the lower bound `1 ≤ ‖x−1‖`). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (only along the coefficient-structure axis — rows 1–3).
Number of weakening opportunities found: **3** (drop `NormedField`→`NormedRing`/`NormedCommRing`, drop `NormedAlgebra ℚ_[p] K`, drop `p`).
Proposed restatement:
```lean
theorem norm_sub_one_eq_one_of_pow {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    {x : K} {m : ℕ} (hpow : ‖x ^ m - 1‖ = 1) (hx : ‖x‖ ≤ 1) : ‖x - 1‖ = 1
```
(Possibly `NormedRing` suffices if `geom_sum_mul` is available without commutativity; `NormedCommRing` is the safe target and matches `Mathlib/Analysis/Normed/Ring/Ultra.lean`'s setting.)
Cost of restatement: **CHEAP** — mechanical: delete the unused instances/`p` and relax `NormedField`→`NormedCommRing`; the proof body is unchanged (every lemma it calls already lives at ring generality).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | already typeclass-based |
| 2 | sequences/metric → filters/topology? | no | — | a pure norm inequality; nothing to filter-ise |
| 3 | construct an object → universal property? | no | — | no constructed object |
| 4 | set+closure predicate → bundled substructure? | no | — | no substructure |
| 5 | vector-space/field-specific → weaken to module/ring? | **yes** | state over `[NormedCommRing K] [IsUltrametricDist K]` | composes with the whole `Mathlib/Analysis/Normed/Ring/Ultra.lean` API at ring generality instead of being trapped in a `ℚ_[p]`-algebra normed-field context |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid? | no | — | `m : ℕ` is the natural exponent index; no generalisation |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (row 5 — and it coincides with the Phase-4b literature weakening).
  - Proposed mathlib-idiomatic restatement: `[NormedCommRing K] [IsUltrametricDist K]` form above.
  - Cost: **CHEAP**.
  - Mathlib downstream this enables: the lemma would sit naturally beside `IsUltrametricDist.norm_add_one_le_max_norm_one` in `Mathlib/Analysis/Normed/Ring/Ultra.lean`; it then applies to integer rings, polynomial/power-series coefficient rings, and any ultrametric normed ring — not just p-adic field extensions. It is reusable by any "lift norm-one across a power" argument (e.g. cyclotomic-unit norm computations).
  - Real mathematical improvement (not just "looks cooler"): yes — it removes three irrelevant hypotheses and lands the result at the generality its proof actually supports.

> Because Phase 4b says STRICTLY NARROWER **and** Phase 4c says a CHEAP modern weakening exists, the verdict gate forbids `YES-add-as-is` and steers toward `YES-but-generalise-first` (reason: both LITERATURE-WEAKENING and MODERN-IDIOM coincide on the ring form).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `norm_sub_one_eq_one_of_pow`

[A] Lean-Finder       (UI-only; not scriptable here)                                  n/a: AI endpoint not callable in this environment; substituted by [B]/[C]/[D]/[E].
[B] Loogle            `‖_ ^ _ - 1‖ = 1`  (and `‖_ - 1‖ = 1`)                            no hits — "39 declarations mentioning Norm.norm, Real, HSub, HPow, Eq; 0 match your pattern(s)".
[C] LeanSearch        "from ‖xⁿ−1‖=1 and ‖x‖≤1 conclude ‖x−1‖=1, ultrametric field"     no usable hit — JSON endpoint not directly fetchable; covered by grep + Loogle + the `Ultra.lean` file read (which lists every lemma in that file).
[D] Grep mathlib src  `norm_(pow_)?sub_one_eq_one`, `sub_one_eq_one_of`, `‖.*\^ .* - 1‖`  no hits for this form — only unrelated decls:
                        • `Complex.norm_sub_one_sq_eq_of_norm_eq_one` (C*-/complex, the *square*)
                        • `Unitary.norm_sub_one_sq_*`, `Unitary.norm_sub_one_lt_two_iff` (C*-algebra)
                        • `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` / `norm_sub_one_two` (cyclotomic **field-norm** `Algebra.norm`, a different "norm")
                        None is the ultrametric `‖·‖` lifting lemma.
[E] Name pattern      `norm_pow_sub_one_eq_one`, `norm_sub_one`                          the dot-notation neighbour `IsPrimitiveRoot.norm_pow_sub_one_eq_one` exists **only in this project** (`Coefficients.lean:211`, declared `_root_.IsPrimitiveRoot.…`), NOT in mathlib. Confirms the surrounding norm-one API here is project-local, not upstreamed.

Searched for both:
  - the user's current form (`NormedField`+`ℚ_[p]`-algebra) — absent;
  - the literature-standard `[NormedCommRing K] [IsUltrametricDist K]` form — also absent (Loogle pattern is type-only and would have caught a ring-level version).

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard ring form). Mathlib has every **building block** but not the packaged implication.

---

### Call sites — `norm_sub_one_eq_one_of_pow`

Internal use count: **1**  (within the PadicLFunctions project, excluding the declaring lines)
External-to-file callers: **0 distinct files** (the sole call is in the *same* file)

| Caller file:line                               | Usage pattern (one-line excerpt)                                  |
|------------------------------------------------|-------------------------------------------------------------------|
| `ValuesAtOne.lean:123`                         | `exact norm_sub_one_eq_one_of_pow hpow1 hεc.le` (inside `norm_pow_sub_one_eq_one_of_unit`) |
| `ValuesAtOne.lean:102` (docstring only)        | `… lifting along `norm_sub_one_eq_one_of_pow` gives …` (prose, not a call) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
  - (none) — no other site re-proves "`‖x−1‖=1` from `‖xᵐ−1‖=1`". The related project lemma `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (`Coefficients.lean:211`, used 4× via dot-notation in `Interpolation/NonTame.lean` and `ValuesAtOne.lean`) proves the *root-of-unity* fact `‖ζ^c−1‖=1` by a **different** route (product `∏(1−ζ^{k+1}) = D`, `Padic.norm_natCast_eq_one_iff`), not by this power-lifting lemma. So this lemma is a distinct, single-purpose step.

**Call-sites signal:** K = 1 internal use, 0 downstream, no inline re-derivation → "possibly the wrong abstraction / could be inlined" **and** "brand-new + barely used". This is a weak composability signal and a NO/BORDERLINE lean per `mathlibable-verdicts.md`'s call-sites table.

---

### Composition check (Phase 6)

Can `norm_sub_one_eq_one_of_pow` be derived from mathlib in ≤3 chained calls?

Attempt 1: `le_antisymm (upper-bound) (lower-bound)` where upper = `(IsUltrametricDist.norm_add_le_max …).trans …` and lower needs `geom_sum_mul` + `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` + `mul_le_of_le_one_left` + a rewrite by `hpow`.
  - Mathlib decls used: `IsUltrametricDist.norm_add_le_max`, `norm_neg`, `norm_one`, `geom_sum_mul`, `norm_mul`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_pow`, `pow_le_one₀`, `mul_le_of_le_one_left`, `le_antisymm`.
  - Result: **fails** as a ≤3-call composition. It requires two separately-derived inequalities (an ultrametric upper bound and a `geom_sum_mul`-driven lower bound) glued by `le_antisymm`, with a `calc` and a `Finset.range`-sum norm bound in between.
  - Notes: this is a genuine ~12-line proof, matching the heuristics-table row "multiple `have`s with non-trivial reasoning between → NO, this is a proof", not the "`Foo.bar (Bar.baz h)`" composable rows.

Conclusion: **NOT-COMPOSABLE** (it is a real proof, not a 1–3 call inlining). → rules out `NO-composable-from-mathlib`.

---

## Verdict: `norm_sub_one_eq_one_of_pow`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the two ingredients (ultrametric isosceles bound; `geom_sum_mul` factorisation) are textbook-standard, but no source packages this combined implication as a named lemma — the hallmark of a small-but-legitimate utility lemma.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 3 CHEAP weakenings (drop `NormedField`→`NormedCommRing`, drop the unused `NormedAlgebra ℚ_[p] K` and prime `p`); Phase 4c confirms the same ring-level form is the modern mathlib idiom.
- Mathlib search (Phase 5): **not in mathlib** under either the current or the ring form (Loogle 0 hits; grep finds only unrelated C*-/complex/cyclotomic-field-norm decls); all building blocks present.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a real ~12-line proof, not a ≤3-call inlining). Call sites: **K = 1** internal, 0 downstream, no inline re-derivation.

**Rationale (why BORDERLINE, not a self-resolving bucket):**

Two facts pull in opposite directions and the resolution turns on a judgement the skill is not licensed to make alone. On the *pro-mathlib* side: the statement is clean, general-purpose, genuinely **absent** from mathlib (Phase 5), and **not** a trivial composition (Phase 6) — so `NO-mathlib-has-it` and `NO-composable-from-mathlib` are both excluded by the gate. On the *anti-standalone* side: it has a single internal call site and zero downstream consumers (Phase 6.0 call-sites table), lives in a project-specific p-adic L-function file, and is a four-line-ish ultrametric micro-lemma — precisely the kind of result for which "does this clear mathlib's bar for a *named* standalone lemma, or should it be inlined / folded into the one caller?" is a taste/policy call. The verdict-bucket reference is explicit that when two buckets genuinely fit, the skill must surface the question rather than silently pick. The single decisive lever — *is this micro-lemma worth a standalone mathlib entry, and at the ring generality?* — is exactly such a question.

The Phase-4 finding sharpens (does not resolve) the call: **if** the answer to Q1 below is "yes, ship it", then the bucket is unambiguously `YES-but-generalise-first` (reason: LITERATURE-WEAKENING + MODERN-IDIOM coincide), and the restatement is already written and CHEAP. A bare `YES-add-as-is` is gate-forbidden here because Phase 4b is STRICTLY NARROWER and Phase 4c offers a real cheap weakening.

**Numbered questions (≤5):**
1. Is this lemma worth a **standalone mathlib entry** at all? It currently has 1 internal call site and 0 downstream consumers — for mathlib it would be justified as a general ultrametric utility (`Mathlib/Analysis/Normed/Ring/Ultra.lean`), not by current usage. Ship it (→ proceed to Q2), or keep it project-local / inline it into its single caller `norm_pow_sub_one_eq_one_of_unit`?
2. If shipping: confirm the **ring generality** target. State as `[NormedCommRing K] [IsUltrametricDist K]` (dropping `NormedField`, `NormedAlgebra ℚ_[p] K`, and the prime `p`)? (CHEAP; proof body unchanged.) Or is `NormedRing` (no commutativity) acceptable/preferred, if `geom_sum_mul` is available there?
3. Naming: keep `norm_sub_one_eq_one_of_pow`, or adopt a mathlib-idiomatic name in the `IsUltrametricDist` namespace, e.g. `IsUltrametricDist.norm_sub_one_eq_one_of_norm_pow_sub_one_eq_one` (or a shorter agreed form)?

**Most likely resolution (if Q1 = "ship it"):** `YES-but-generalise-first`. Proposed restatement (already CHEAP — Phase 4b/4c):
```lean
theorem norm_sub_one_eq_one_of_pow {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    {x : K} {m : ℕ} (hpow : ‖x ^ m - 1‖ = 1) (hx : ‖x‖ ≤ 1) : ‖x - 1‖ = 1 := by
  -- existing proof body transfers verbatim
  sorry
```
Mathlib downstream this enables: lands beside `IsUltrametricDist.norm_add_one_le_max_norm_one` in `Mathlib/Analysis/Normed/Ring/Ultra.lean`; reusable for cyclotomic-unit / root-of-unity norm computations and any ultrametric normed ring, not just p-adic field extensions.

**Next action:** user answers Q1–Q3, then re-run `/mathlibable norm_sub_one_eq_one_of_pow` (or, if Q1 = ship, run `/generalise norm_sub_one_eq_one_of_pow` to land the `[NormedCommRing K] [IsUltrametricDist K]` form, then `/cleanup` + `/pre-submit` before the mathlib PR). If Q1 = keep local, inline it into `norm_pow_sub_one_eq_one_of_unit` and delete the standalone lemma.

---

## Next step

User answers Q1–Q3 above; then re-run `/mathlibable norm_sub_one_eq_one_of_pow`. If "ship it", the verdict becomes `YES-but-generalise-first` with the CHEAP ring-level restatement already prepared — hand to `/generalise`, then `/cleanup` + `/pre-submit`. If "keep local", inline into the single caller and drop the standalone lemma.
