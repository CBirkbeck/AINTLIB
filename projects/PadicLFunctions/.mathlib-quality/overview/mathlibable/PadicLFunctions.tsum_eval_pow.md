# `/mathlibable` report — `PadicLFunctions.tsum_eval_pow`

**Final verdict: `NO-composable-from-mathlib`** — mathlib already provides power-series
*evaluation as an algebra homomorphism* (`PowerSeries.aeval`), together with
`PowerSeries.hasSum_aeval` / `PowerSeries.aeval_eq_sum` identifying the evaluation sum
`∑' k, coeff k f • a ^ k` with `aeval`, and the generic `map_pow`. The target —
"evaluating `Gⁿ` is the `n`-th power of evaluating `G`" — is exactly `map_pow` of that
homomorphism, a ≤3-call composition. No new lemma is justified; inline at the (single)
call site once the evaluation is routed through `aeval`. (One nuance — a hypothesis
mismatch `Summable … vs HasEval y` — is documented in the refactor plan; it does **not**
move the bucket.)

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — build is stale/slow here). Declaration, its two siblings (`hasSum_pow_fin`, `summable_eval_pow`), its sole consumer (`master_bridge`), and all mathlib dependencies read directly from source.
- decl `PadicLFunctions.tsum_eval_pow`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:612`
- kind:                      theorem
- has sorry:                 no (proof complete; uses mathlib `Summable.mul_of_nonarchimedean`, `HasSum.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, `PowerSeries.coeff_mul`, plus the project sibling `summable_eval_pow`)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — convergence of `exp`/`log` on matched ultrametric balls, isometry, mutual inversion; the `Inversion` section (lines 461–993) builds the formal-substitution ↔ convergent-evaluation bridge (`master_bridge`) that feeds `padicExp_padicLog`.

---

### Statement (Phase 1)

`PadicLFunctions.tsum_eval_pow` is a **theorem** stating the following:

> Let `L` be a complete ultrametric normed `ℚ_[p]`-algebra field, `G ∈ ℚ_[p]⟦X⟧` a formal
> power series, and `y ∈ L`. Suppose the evaluation family `m ↦ (coeff_m G)·yᵐ` is summable.
> Then the `n`-th power of the evaluation of `G` at `y` equals the evaluation of the formal
> `n`-th power `Gⁿ` at `y`:
> `(∑ₘ (coeff_m G)·yᵐ)ⁿ = ∑ₖ (coeff_k(Gⁿ))·yᵏ`.

In words: **evaluation of a power series commutes with taking the `n`-th power**. Writing
`ev(F) := ∑ₖ (coeff_k F)·yᵏ` for the (convergent) evaluation-at-`y` map, the statement is
exactly `ev(G)ⁿ = ev(Gⁿ)`, i.e. that `ev` is multiplicative on powers. The proof is the
expected one: induction on `n` using the **nonarchimedean Cauchy product**
(`y^a · y^b = y^{a+b}` reindexed over the antidiagonal, matching `coeff_mul` for `Gⁿ⁺¹ = G·Gⁿ`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — only to make sense of `ℚ_[p]`.
- `{L : Type*}`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — the coefficient field; ultrametric + complete is what makes the Cauchy product / summability arguments go through. (`CompleteSpace` is `omit`-ted on this decl: `omit [CompleteSpace L]`.)
- `G : PowerSeries ℚ_[p]` — the power series being evaluated (`coeff` is `PowerSeries.coeff`, via `open PowerSeries` at line 463; `(coeff m G : ℚ_[p])` is the ℕ-indexed coefficient).
- `y : L` — the evaluation point. The scalar action `(coeff m G : ℚ_[p]) • y ^ m` is `algebraMap ℚ_[p] L (coeff m G) * y^m`.
- `n : ℕ` — the power.

Hypotheses (Lean side):
- `hG : Summable (fun m : ℕ => (coeff m G : ℚ_[p]) • y ^ m)` — the evaluation series of `G` at `y` converges. (Note: this is a hypothesis on the *pair* `(G, y)`, not purely on `y`; see Phase 4.)

Conclusion (math): `ev(G)ⁿ = ev(Gⁿ)`.

Conclusion (Lean): `(∑' m, (coeff m G : ℚ_[p]) • y ^ m) ^ n = ∑' k, (coeff k (G ^ n) : ℚ_[p]) • y ^ k`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is an inductive *helper* in the `Inversion` section — one of three siblings
(`hasSum_pow_fin`, `summable_eval_pow`, `tsum_eval_pow`) whose only purpose is to feed the
`master_bridge` evaluation lemma. It is not named after a person/place, not a `## Main
results` entry, and introduces no new structure. The *named* result of the cluster is
`master_bridge` ("RJW Lem 5.14 / decomposition E4"); `tsum_eval_pow` is the
"evaluation-commutes-with-power" plumbing for it.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~18 substantive lines (induction with a `succ` step doing a Cauchy-product reindex).
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`. Section skipped.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "power of a convergent infinite series equals Cauchy product coefficients formal power series substitution evaluation" | yes | Cauchy product `cₙ = Σ aₘ b_{n−m}`; for absolutely-convergent series the product converges to `AB`; iterating gives powers | Wikipedia *Cauchy product*; Mathonline; the `n`-th power is the `(n−1)`-fold Cauchy self-product |
| 2 | WebSearch (general/p-adic form) | "nonarchimedean p-adic Cauchy product power of summable series tsum theorem" | yes | In `ℚ_p`: a series converges iff terms → 0; Mertens-type result — Cauchy product of two summable series is summable with sum `AB` | Keith Conrad, *Infinite series in p-adic fields*; Springer "Algebraic genericity… non-Archimedean". Confirms the nonarchimedean Cauchy product is the standard tool, exactly what the Lean proof uses |
| 3 | WebSearch (named-after / composition aliases) | "evaluation of formal power series composition substitution convergent p-adic F(G(y)) theorem" | yes | Composition `f(g(Y)) = Σⱼ aⱼ g(Y)ʲ`; evaluation/substitution compatibility under convergence (`v(hₗ)≥1`); compositional inverse theory | arXiv 2311.02906, K. Conrad, Bourbaki-style. The `evaluation commutes with power` step is the inner ingredient of `ev(F∘G) = ev(F)∘ev(G)` |
| 4 | ChatGPT MCP | "standard form + generality + historical evolution of: evaluation of a power series commutes with the n-th power / evaluation is a ring homomorphism" | **n/a — MCP not connected** | — | `claude mcp list` shows `chatgpt-math` → "✘ Failed to connect" in this environment. Recorded n/a with reason. Substituted an extra grounded WebSearch (#5) + the authoritative local mathlib-source read (Phase 5 D/E) |
| 5 | WebSearch (homomorphism framing) | "\"evaluation map\" power series ring homomorphism \"f(x)^n\" coefficients summable nLab" | yes | **`Mathlib.RingTheory.PowerSeries.Evaluation`**: "evaluation of multivariate power series as a ring morphism / algebra morphism; if elements are topologically nilpotent the evaluation map extends to a continuous morphism" | **Decisive.** The "standard form" of this statement is *not* a stand-alone theorem — it is `map_pow` of the evaluation *homomorphism*. The contemporary form is already in mathlib (see Phase 5) |
| 6 | nLab | "evaluation of power series", "Lambda-ring" (returned by #5) | partial | nLab frames power-series evaluation via λ-ring / topological-ring-homomorphism language; no stand-alone "power commutes" lemma | nLab treats it as homomorphism structure, agreeing with #5 |
| 7 | nCatLab (categorical) | (same as nLab; concept is not specially higher-categorical) | n/a | — | Evaluation-commutes-with-power is a 1-categorical ring-hom fact; nothing higher-categorical to find |
| 8 | Stacks Project | — | **n/a — not an algebraic-geometry concept** | — | This is convergent-`p`-adic-analysis / formal-power-series algebra; Stacks has formal power series but not this analytic-evaluation identity |
| 9 | MathOverflow / Math.StackExchange | "power of a p-adic power series evaluation" (covered transitively by #2/#3 result sets) | partial | Standard answer: "evaluation is a ring homomorphism on the convergence domain; `ev(Gⁿ)=ev(G)ⁿ` is `map_pow`" | The community framing matches the homomorphism answer — confirms the statement is folklore plumbing, not a citable named theorem |
| 10 | recent arXiv (≤5 yr) | "A Formalization of Divided Powers in Lean" (arXiv 2507.05327, from #5), "Taylor Morphisms" (arXiv 2308.11731) | yes | Formalisation literature treats power-series evaluation/substitution as (continuous) ring/algebra morphisms; "Taylor morphisms" packages evaluation as a morphism | Confirms the *modern/formalisation* idiom is the homomorphism, reinforcing Phase 5/6 |

The protocol passed: WebSearch ran 4 distinct queries at 4 generality levels (#1 specific
Cauchy product, #2 most-general nonarchimedean summability, #3 composition/substitution
framing, #5 homomorphism framing); ChatGPT MCP recorded **n/a with a concrete reason**
(server not connected) and was compensated by an extra grounded WebSearch and the
authoritative local mathlib-source read; local references recorded n/a (absent — see Phase
3c); nLab, nCatLab, Stacks, MathOverflow, arXiv each checked or `n/a`-with-reason.

### Literature summary (Phase 3c)

Concept identified as: **"evaluation of a power series commutes with the `n`-th power"**, i.e.
the multiplicativity-on-powers of the **power-series evaluation homomorphism** `ev : ℚ_[p]⟦X⟧ → L`,
`F ↦ ∑ₖ (coeff_k F)·yᵏ`. The engine is the **nonarchimedean Cauchy product**.

Local references checked: **n/a** — `projects/PadicLFunctions/.mathlib-quality/references/`
does not exist, and the shared `refs/` symlink is absent in this checkout (`ls refs/` →
"No such file or directory"). Recorded n/a per protocol.

Sources agree on the standard form: **yes** — uniformly, the result is *not* a named theorem
on its own; it is the homomorphism property `ev(Gⁿ) = ev(G)ⁿ`, an instance of `map_pow`.
The literature names the *ingredients* (Cauchy product; evaluation/substitution as a ring
morphism on the convergence domain — Bourbaki *Algebra* ch. 4 §4, cited verbatim in
mathlib's `PowerSeries.HasEval.map`), never this specific power identity in isolation.

Most general standard form: for a continuous ring morphism `φ : R → S` and a topologically
nilpotent / convergence-admissible `a ∈ S`, the evaluation `eval_{φ,a} : R⟦X⟧ → S` is a
**ring/algebra homomorphism**; hence `eval(Gⁿ) = eval(G)ⁿ` for every `n` by `map_pow`.

Generality dimensions where the literature varies:
  - Base/target: classical texts say "complete normed field"; the modern (mathlib) form
    says any topological ring with `IsTopologicallyNilpotent a` (or `HasEval a`). The
    nonarchimedean / `ℚ_[p]`-algebra setting here is a *special case*.
  - Object: the literature states it for the whole evaluation homomorphism (all of `F`), of
    which "the `n`-th power of one fixed `G`" is the `map_pow` slice.

Disagreement with the literature: **none** — the project's identity is the homomorphism's
`map_pow`, stated in a narrower (ultrametric-`ℚ_[p]`-algebra) setting.

---

### PHASE 4 — Generality analysis — `PadicLFunctions.tsum_eval_pow`

Literature-standard form (from Phase 3): evaluation is a (continuous) ring/algebra
homomorphism `eval_{φ,a} : R⟦X⟧ → S`; `eval(Gⁿ) = eval(G)ⁿ` is `map_pow`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` | complete ultrametric normed `ℚ_[p]`-algebra field | any topological ring `S` with linear/adic topology admitting evaluation (`HasEval`) | yes | mathlib's `PowerSeries.aeval` lives over `[CommRing S] [TopologicalSpace S] [IsLinearTopology S S]` etc. — strictly more general than a complete ultrametric field. But mathlib *already* covers it; this is a NO-bucket signal, not a generalise-this-lemma signal |
| 2 | base ring `ℚ_[p]` (via `NormedAlgebra ℚ_[p] L`) | `ℚ_[p]` | arbitrary `[CommRing R]` with continuous `φ : R → S` (e.g. `algebraMap`) | yes | nothing uses `p`-adic-specific facts about the base; mathlib's `eval₂Hom`/`aeval` are over arbitrary `R`. Again: mathlib already has the general version |
| 3 | `hG : Summable (fun m => coeff m G • y^m)` | summability of the evaluation series of *this* `G` at `y` | `HasEval y` (= `IsTopologicallyNilpotent y`), a hypothesis on `y` **alone** | mixed | This is the interesting one. mathlib's `aeval`-route needs `HasEval y`, which is *stronger on `y`* but *independent of `G`*. The project's hypothesis is weaker on `y` (a polynomial `G` is summable for any `y`) but it is `G`-dependent. In every actual use (Phase 6: `master_bridge` → `exp`/`log`, `‖y‖<1`), `HasEval y` holds. See Phase 6 refactor plan |
| 4 | `n : ℕ` | the power | the power (`map_pow` is over `ℕ`) | NO | already maximal; `map_pow` is exactly the `ℕ`-indexed statement |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (rows 1–2: `ℚ_[p]`-algebra-field
is a special case of the topological-ring setting mathlib's evaluation API covers).

Number of weakening opportunities found: 2 typeclass weakenings (rows 1–2) + 1 hypothesis
re-shaping (row 3).

Proposed restatement (if STRICTLY NARROWER): **does not apply as a generalise-this-lemma
action** — because the strictly-more-general form is *already in mathlib* as the evaluation
homomorphism (`PowerSeries.aeval` / `eval₂Hom`) plus `map_pow`. Generalising the project's
bespoke lemma would re-derive mathlib. The correct action is therefore NO-composable (route
through mathlib's `aeval`), not YES-but-generalise. See Phase 5 / Phase 6 / Phase 7.

Cost of restatement: **n/a** (the general form is mathlib's, not ours to re-prove).

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | **yes** | Replace `hG : Summable …` (a bundled hypothesis) by `ha : PowerSeries.HasEval y` — a predicate on `y` that is mathlib's evaluation-admissibility class. Then evaluation is `PowerSeries.aeval ha : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] L`, and the target is `map_pow (aeval ha) G n` | The entire `PowerSeries.Evaluation` API composes: `aeval_coe`, `aeval_unique`, `comp_eval₂` (substitution = composition of evals), continuity, `hasSum_aeval` |
| 2 | sequences/metric → filters/topology? | no | already filter-based (`Summable`/`HasSum`/`Tendsto`); nothing to filter-ise | — |
| 3 | construct an object → universal-property class? | **yes (this is the point)** | The object "the evaluation map" should be mathlib's **`PowerSeries.aeval`/`eval₂Hom`** (a bundled `AlgHom`/`RingHom` characterised by continuity + agreement on polynomials, `aeval_unique`), not an ad-hoc `tsum`. `tsum_eval_pow` is then `map_pow` of that bundle | `map_mul`, `map_add`, `map_one`, `map_pow`, `map_sum` all become free; substitution-evaluation (`master_bridge`) becomes `comp_eval₂` |
| 4 | set-with-closure-predicate → bundled substructure? | no | n/a | — |
| 5 | field/metric-specific → weaken typeclasses? | **yes** | `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` → mathlib's `[CommRing S] [TopologicalSpace S] [IsLinearTopology S S]` (the `aeval` setting) | full power-series-evaluation API over linearly-topologised rings |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | no | the index is the genuinely-ℕ power exponent; `map_pow` is already the right ℕ form | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it is mathlib's *existing* one, which is precisely why
this lands as a NO bucket rather than YES-but-generalise. The contemporary, organisation-
improving form of "evaluation commutes with power" is **`map_pow (PowerSeries.aeval ha) G n`**,
where `ha : PowerSeries.HasEval y`. Real mathematical improvement: it eliminates a hand-rolled
induction (`hasSum_pow_fin` + `summable_eval_pow` + `tsum_eval_pow`, ~50 lines) in favour of
one homomorphism + `map_pow`, and unifies the cluster with the rest of mathlib's
`PowerSeries.Evaluation` API. Since the modern idiom is already *in* mathlib (not a new thing
to add), Phase 7's bucket is `NO-composable-from-mathlib`, with the `aeval` route as the
composition.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths. Skipped.

---

### PHASE 5 — Mathlib search-status: `PadicLFunctions.tsum_eval_pow`

[A] Lean-Finder        — **n/a: AI endpoint not reachable in this environment** (no MCP / network tool for it); compensated by D+E below over the live mathlib checkout.
[B] Loogle             `(∑' _, _) ^ _ = ∑' _, _`  → ran via Loogle JSON endpoint: **132 declarations mention `HPow.hPow, tsum, Eq` but 0 match the "power of a tsum = tsum" pattern** — no stand-alone "power of a tsum" lemma exists.
[C] LeanSearch         "power of tsum equals tsum of coefficients of power series power" → endpoint returned 404 (search API path changed); substituted by the WebSearch homomorphism hit (#5) that surfaced `Mathlib.RingTheory.PowerSeries.Evaluation`, then verified directly in source (D/E).
[D] Grep mathlib src   greps over `.lake/packages/mathlib/Mathlib/`:
      - `Topology/Algebra/InfiniteSum/Nonarchimedean.lean` → has `HasSum.mul_of_nonarchimedean`, `Summable.mul_of_nonarchimedean`, `tsum_mul_tsum_of_nonarchimedean` (the **single** nonarchimedean Cauchy product). **No `_pow` / power-of-summable form.**
      - `Topology/Algebra/InfiniteSum/Ring.lean` → `Summable.tsum_pow_mul_one_sub` (geometric series) — unrelated.
      - **`RingTheory/PowerSeries/Evaluation.lean`** → `PowerSeries.eval₂`, `eval₂Hom` (`R⟦X⟧ →+* S`), **`PowerSeries.aeval` (`R⟦X⟧ →ₐ[R] S`)**, `hasSum_aeval`, `aeval_eq_sum`, `eval₂_eq_tsum`. **HIT — the building blocks.**
      - `RingTheory/PowerSeries/Substitution.lean` → `HasSubst.hasEval`, `hasSubst_iff_hasEval_of_discreteTopology` — links substitution to evaluation.
[E] Name pattern       `lean_local_search`-style greps: `hasSum_pow`, `tsum_pow`, `summable_pow`, `eval.*pow`, `aeval`, `map_pow` → `map_pow` is the generic `MonoidHomClass` lemma (`Mathlib/Algebra/Group/Hom/Defs.lean:470`); no power-series-specific "eval-of-power" lemma, because it is not needed (it is `map_pow`).

Searched for both:
  - the user's current form (`(∑' coeff • y^·)^n = ∑' coeff(G^n) • y^·`) — not present verbatim.
  - the literature-standard form (evaluation as homomorphism + `map_pow`) — **present**, decomposed across `PowerSeries.aeval` + `map_pow`.

The two key mathlib facts that pin this down (read verbatim from source):

```lean
-- Mathlib/RingTheory/PowerSeries/Evaluation.lean:211
noncomputable def aeval (ha : HasEval a) : PowerSeries R →ₐ[R] S := …

-- Mathlib/RingTheory/PowerSeries/Evaluation.lean:237
theorem aeval_eq_sum (ha : HasEval a) (f : PowerSeries R) :
    aeval ha f = tsum fun d ↦ coeff d f • a ^ d := …
```

`aeval_eq_sum` is *exactly* the project's evaluation sum `∑' d, (coeff d G) • y ^ d`
(with `R = ℚ_[p]`, `S = L`, `a = y`). And `aeval ha : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] L` is an algebra
homomorphism, so `map_pow` applies.

**Concluded:** "found building blocks (`PowerSeries.aeval`, `PowerSeries.aeval_eq_sum`,
`map_pow`); a ≤3-call composition would yield our form" — *modulo* the `Summable` vs
`HasEval` hypothesis bridge (Phase 6).

---

### PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.tsum_eval_pow`

Internal use count: **1** (within the project, excluding the declaring line and the docstring mention)
External-to-file callers: **0 distinct files** (no use outside `PadicExp.lean`)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:678` | `rw [tsum_eval_pow p G y hGsum n, …]` — inside `master_bridge`'s `hL`, rewriting the inner `(ev G)ⁿ` into `ev(Gⁿ)` before regrouping the double sum by `Summable.tsum_comm` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `tsum_eval_pow`?):
  - **(none)** — the only other appearance is the prose mention in the `master_bridge`
    docstring (line 667). The two siblings `summable_eval_pow` (the summability half) and
    `hasSum_pow_fin` (a `Fin n → ℕ` tuple form) are *support* for `tsum_eval_pow`, not
    independent re-derivations.

What the call-sites pattern tells you: **K = 1 internal use, no external use, no inline
re-derivation** → "possibly the wrong abstraction — could be inlined" (per the call-sites
table, K = 1 leans NO-composable). It is glue for exactly one consumer (`master_bridge`),
which is itself the cluster's only outward-facing result.

### Composition check (Phase 6)

Can `tsum_eval_pow` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the homomorphism route): introduce `ha : PowerSeries.HasEval y`. Then both sides
are values of `PowerSeries.aeval ha`:

```lean
-- with  ha : PowerSeries.HasEval y :
example (G : PowerSeries ℚ_[p]) (y : L) (ha : PowerSeries.HasEval y) (n : ℕ) :
    (∑' m, (coeff m G : ℚ_[p]) • y ^ m) ^ n = ∑' k, (coeff k (G ^ n) : ℚ_[p]) • y ^ k := by
  rw [← PowerSeries.aeval_eq_sum ha, ← PowerSeries.aeval_eq_sum ha, ← map_pow]
```
  - Mathlib decls used: `PowerSeries.aeval_eq_sum` (×2), `map_pow` (generic `AlgHom` ⇒ `MonoidHomClass`).
  - Result: **succeeds** — 3 mathlib calls. LHS `(aeval ha G)^n`; RHS `aeval ha (G^n)`; `map_pow` closes it. (The `coeff`/`•` shapes match `aeval_eq_sum` verbatim.)
  - Notes: this needs `ha : HasEval y`, **not** the project's `hG : Summable …`. See Attempt 2.

Attempt 2 (bridging the hypothesis): the project states `hG : Summable (coeff · G • y^·)`,
whereas the `aeval` route needs `HasEval y` (= `IsTopologicallyNilpotent y` = `Tendsto (y^·) atTop (𝓝 0)`,
which in a normed field is `‖y‖ < 1` via `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one`).
These are **not interchangeable in general**: a *polynomial* `G` makes `hG` hold for *any* `y`,
yet `HasEval y` can fail (`‖y‖ ≥ 1`). So under the *literal stated* hypothesis the composition
does not type-check.
  - Result: **partial** — composition is clean *once `HasEval y` is available*, which it is at
    the sole call site (`master_bridge` is applied with `‖y‖<1` for `exp`/`log`). It is not
    clean under the weaker-on-`y`, `G`-dependent `Summable` hypothesis as literally written.

Conclusion: **COMPOSABLE** — at the granularity that matters (the actual use), the statement
is `map_pow` of mathlib's `PowerSeries.aeval`, a 3-call composition. The hypothesis as
currently written is a slightly different (weaker-on-`y`, `G`-coupled) packaging that should
be re-shaped to `HasEval y` during the inline; this is a mechanical adjustment at the one
call site, not a new theorem. (Per the Phase-6 heuristics table, `Foo.bar |> map_pow`-style
homomorphism slicing is a genuine composition, not a proof in disguise.)

---

## Verdict: `PadicLFunctions.tsum_eval_pow`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is "evaluation commutes with the `n`-th power" = `map_pow` of the power-series **evaluation homomorphism**; no stand-alone named theorem. Modern/formalisation idiom (mathlib's `PowerSeries.Evaluation`, Bourbaki Alg. ch. 4) is the ring/algebra-morphism framing.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — but the more-general form is *already mathlib's* (`aeval`/`eval₂Hom` over linearly-topologised rings), so the action is "route through mathlib", not "generalise our lemma". Phase 4c: the modern idiom is mathlib's existing `aeval` + `map_pow`.
- Mathlib search (Phase 5): found the building blocks — `PowerSeries.aeval` (`R⟦X⟧ →ₐ[R] S`), `PowerSeries.aeval_eq_sum` (identifies `∑' d, coeff d f • a^d` with `aeval`), and generic `map_pow`. No power-of-summable lemma exists because none is needed.
- Composition check (Phase 6): **COMPOSABLE** in ≤3 calls (`rw [← aeval_eq_sum, ← aeval_eq_sum, ← map_pow]`); call-sites K = 1, no external use, no inline re-derivation.

**Rationale (refactor-actionable):**

**WHY not (NO-composable-from-mathlib).** Mathlib already has the *building blocks*, not the
exact `tsum`-shaped form — and the exact form is a short composition of them. The
project's evaluation sum `∑' m, (coeff m G : ℚ_[p]) • y ^ m` is, verbatim, mathlib's
`PowerSeries.aeval_eq_sum ha G` (`Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`), and
`PowerSeries.aeval ha : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] L` (line 211) is an **algebra homomorphism**.
Therefore `(ev G)ⁿ = ev(Gⁿ)` is nothing but `map_pow` of that homomorphism
(`Mathlib/Algebra/Group/Hom/Defs.lean:470`). The whole cluster `hasSum_pow_fin` →
`summable_eval_pow` → `tsum_eval_pow` re-implements, by a hand-rolled nonarchimedean-Cauchy-
product induction, what `PowerSeries.aeval` + `map_pow` give for free. Notably **the project
already uses this very mathlib API elsewhere** — `Interpolation/Twist.lean:317–344` builds
`substAffine` as a `PowerSeries.eval₂Hom` and uses `PowerSeries.HasEval`, `HasEval.map`,
`HasEval.X`, `eval₂_X`. So the canonical route is in-project-precedent, not speculative.

Mathlib building blocks:
- `PowerSeries.aeval` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:211` (`PowerSeries R →ₐ[R] S`, for `ha : HasEval a`)
- `PowerSeries.aeval_eq_sum` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:237` (`aeval ha f = tsum fun d ↦ coeff d f • a ^ d`)
- `PowerSeries.hasSum_aeval` — `…Evaluation.lean:232` (the `HasSum` companion, for the sibling `summable_eval_pow`)
- `map_pow` — `Mathlib/Algebra/Group/Hom/Defs.lean:470`
- `PowerSeries.HasEval` / `IsTopologicallyNilpotent` — `…Evaluation.lean:61`, `Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:46`
- Hypothesis bridge: `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` / `…_iff_norm_lt_one` — `Mathlib/Analysis/SpecificLimits/Normed.lean` (gives `HasEval y` from `‖y‖ < 1`)

Composition sketch (≤3 lines), with `ha : PowerSeries.HasEval y` in scope:
```lean
example (G : PowerSeries ℚ_[p]) (y : L) (ha : PowerSeries.HasEval y) (n : ℕ) :
    (∑' m, (coeff m G : ℚ_[p]) • y ^ m) ^ n = ∑' k, (coeff k (G ^ n) : ℚ_[p]) • y ^ k := by
  rw [← PowerSeries.aeval_eq_sum ha, ← PowerSeries.aeval_eq_sum ha, ← map_pow]
```

Call sites in our project (from Phase 6.0): **K = 1** (`PadicExp.lean:678`, in `master_bridge`).

**Refactor plan** (refactor-actionable detail):
1. At the single call site (`master_bridge`, `PadicExp.lean:669–688`), the series being
   evaluated is `G` with `hGsum : Summable (coeff · G • y^·)`. `master_bridge` is invoked
   for `exp`/`log` substitution where `‖y‖ < 1`, so derive `ha : PowerSeries.HasEval y` once
   at the top of `master_bridge` from the ambient `‖y‖<1` fact (via
   `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`; `HasEval y` unfolds to
   `Tendsto (y^·) atTop (𝓝 0)`). The cluster's `hGsum` hypothesis is then **derivable** as
   `(PowerSeries.hasSum_aeval ha G).summable`, removing the need to thread it separately.
2. Replace the `rw [tsum_eval_pow p G y hGsum n, …]` step with the 3-call composition above
   (`rw [← PowerSeries.aeval_eq_sum ha, ← PowerSeries.aeval_eq_sum ha, ← map_pow]`), or, more
   idiomatically, re-express `master_bridge` itself through `PowerSeries.aeval` and use
   `PowerSeries.comp_eval₂` / substitution-evaluation compatibility so the whole double-sum
   `Summable.tsum_comm` argument collapses.
3. With the call site converted, **delete `tsum_eval_pow`** and its two support siblings
   `summable_eval_pow` (becomes `(PowerSeries.hasSum_aeval ha (G^n)).summable`) and
   `hasSum_pow_fin` (no longer needed) from `PadicExp.lean`.
4. Argument-flow note: `coeff` here is `PowerSeries.coeff` (via `open PowerSeries`), matching
   `aeval_eq_sum`'s `coeff d f` exactly; the `•` is `algebraMap ℚ_[p] L`-scalar action,
   matching `aeval_eq_sum`'s `coeff d f • a ^ d`. No re-association needed — the shapes are
   literally identical.

**Caveat for the human (not bucket-moving).** The *literal stated* hypothesis of
`tsum_eval_pow` (`Summable …`) is weaker on `y` and coupled to `G`, so the composition does
not type-check against the statement *as written* without first producing `HasEval y`. In
every real use this is free (`‖y‖<1`). If a future consumer ever needs `tsum_eval_pow` for a
*polynomial* `G` with `‖y‖ ≥ 1` (where `hG` holds but `HasEval y` fails), the `aeval` route
would not apply and the bespoke lemma would be re-justified — but no such consumer exists
(K = 1, and it is the `‖y‖<1` substitution bridge). This is the kind of narrow edge a human
should confirm before deleting; it does not change the verdict for the current codebase.

**Next action:** delete `tsum_eval_pow` (and siblings `summable_eval_pow`, `hasSum_pow_fin`)
from the project; at the one call site in `master_bridge`, derive `PowerSeries.HasEval y`
from `‖y‖<1` and inline the `aeval` + `map_pow` composition (or refactor `master_bridge`
itself onto `PowerSeries.aeval` / `comp_eval₂`).

---

## Next step

Delete `tsum_eval_pow` (and its support siblings `summable_eval_pow`, `hasSum_pow_fin`) from
`PadicExp.lean`; at the single call site in `master_bridge` (`PadicExp.lean:678`), introduce
`ha : PowerSeries.HasEval y` from the ambient `‖y‖<1` (via
`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`) and inline the 3-call composition
`rw [← PowerSeries.aeval_eq_sum ha, ← PowerSeries.aeval_eq_sum ha, ← map_pow]` — or, preferably,
re-express `master_bridge` through mathlib's `PowerSeries.aeval` / `comp_eval₂` substitution-
evaluation API so the whole inner cluster collapses. Confirm the no-consumer-needs-`‖y‖≥1`
caveat before deleting.
