# `/mathlibable` report — `PadicLFunctions.summable_eval_pow`

**Final five-bucket verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING + MODERN-IDIOM / Bourbaki 2.0).

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task instruction); **reasoned from source**. The decl + its two load-bearing dependencies (`Summable.mul_of_nonarchimedean`, `summable_sum_mul_antidiagonal_of_summable_mul`) were read directly from `.lake/packages/mathlib/` and from the project source.
- decl `PadicLFunctions.summable_eval_pow`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:586`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14): `exp`/`log` convergence and inversion on matched balls of a complete nonarchimedean normed `ℚ_[p]`-algebra field; defines `x^s := exp(s·log x)`.

Ambient context (file-level `variable`s):
```
variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]
```
The decl carries `omit [CompleteSpace L]` (completeness is not used). `open PowerSeries` is in scope (line 463), so `coeff m G` means `PowerSeries.coeff ℚ_[p] m G`.

---

### Statement (Phase 1)

`PadicLFunctions.summable_eval_pow` is **a theorem** stating the following:

> Let `L` be a complete ultrametric (nonarchimedean) normed field that is a normed `ℚ_[p]`-algebra, let `G ∈ ℚ_[p]⟦X⟧` be a formal power series, and let `y ∈ L`. Suppose the evaluation family `m ↦ (coeff_m G)·yᵐ` is summable in `L`. Then for every `n ∈ ℕ`, the evaluation family of the `n`-th power `G^n`, namely `k ↦ (coeff_k(Gⁿ))·yᵏ`, is also summable in `L`.

In words: **if a power series can be evaluated (summably) at `y`, then so can every power of it.** This is the *well-definedness / summability half* of the statement "evaluation at `y` is multiplicative" (`eval(Gⁿ) = (eval G)ⁿ`); the value half is the sibling `tsum_eval_pow` (line 612).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L` with `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` — a complete (here `omit`-ted) nonarchimedean normed field extension of `ℚ_[p]`. The ultrametric instance yields `NonarchimedeanRing L` (the file's first `instance`), which is what the proof actually consumes.
- `G : PowerSeries ℚ_[p]` — the series whose powers are evaluated.
- `y : L` — the evaluation point.
- `n : ℕ` — the power.

Hypotheses (Lean side):
- `hG : Summable fun m : ℕ => (coeff m G : ℚ_[p]) • y ^ m` — the base series is summably evaluable at `y`.

Conclusion (math): the evaluation family of `Gⁿ` at `y` is summable.

Conclusion (Lean): `Summable fun k : ℕ => (coeff k (G ^ n) : ℚ_[p]) • y ^ k`.

Proof shape (read from source): induction on `n`. Base case `n = 0`: `G⁰ = 1`, the family is `k ↦ if k=0 then 1 else 0`, summable by `summable_of_ne_finset_zero` + `Summable.congr`. Step: with `f m = (coeff m G)·yᵐ` and `g k = (coeff_k(Gⁿ))·yᵏ`, form the product family `(a,b) ↦ f a · g b`, summable by **`Summable.mul_of_nonarchimedean hG ih`**; then collapse the antidiagonal with **`summable_sum_mul_antidiagonal_of_summable_mul`**, and `.congr` it to the `Gⁿ⁺¹` family using `pow_succ'`, `coeff_mul`, `Finset.sum_smul`, `smul_mul_smul_comm`, `pow_add`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (technically) — **with a BIG conceptual halo.**
Reason: it is a helper lemma feeding `tsum_eval_pow` and the substitution/composition machinery (not itself a `## Main results` headline). But it is one piece of a genuinely central, named classical fact — *evaluation of a power series at a (summable) point is a multiplicative / ring homomorphism* — so the literature is rich and the generality question is live. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check **n/a** (skipped). The body is a multi-step induction, not a one-liner.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "nonarchimedean summable families Cauchy product summable power series evaluation ring homomorphism" | yes | In a nonarchimedean Cauchy-complete ring, the product (Cauchy convolution) of two unconditionally-summable families is summable with sum = product of sums | Confirms the exact `mul_of_nonarchimedean` mechanism; nonarchimedean unconditional summability extends classical results. |
|  2 | WebSearch (general form)         | "formal power series substitution evaluation continuous ring homomorphism convergent p-adic multiplicative power" | yes | When the element is topologically nilpotent / the powers → 0, **evaluation extends uniquely to a continuous (ring) morphism**; multiplication continuous via Cauchy product | Wikipedia *Formal power series* / *Restricted power series*, PlanetMath, nLab. This is the maximally-general framing: evaluation is a continuous **ring hom**, hence multiplicative — `eval(Gⁿ)=(eval G)ⁿ` is `map_pow`. |
|  3 | WebSearch (named-after / aliases)| "power series substitution morphism of complete topological rings well-defined summability nLab" | yes | Substitution/evaluation into a complete topological ring is a (unique adic) algebra map; "summable iff terms → 0" | aliases: *substitution*, *evaluation*, *specialization homomorphism*. |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution) | **n/a** | — | **ChatGPT MCP not configured in this environment** (`/setup-chatgpt` not run; no MCP tool surfaced). Compensated by an extra WebSearch (#10) and three source fetches. |
|  5 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | **n/a** | — | No `references/` dir and no `refs/` store present. Recorded n/a per protocol. The module docstring's own citations (RJW Lem 5.14 / Cassels §12 / Washington §5.1) are about exp/log, not this generic evaluation lemma. |
|  6 | nLab                             | fetched `ncatlab.org/nlab/show/power+series` ("Functional substitution and inversion") | yes | "there exists **a unique adic algebra map** `R[[x₁,…,xₙ]] → S`" for an adic `R`-algebra `(S,I)` with substituends in `I` | The abstract universal-property statement: substitution into a complete (adic) algebra is an **algebra homomorphism** ⇒ multiplicative. Does not phrase it for normed (non-adic) fields, but the homomorphism content is exactly the standard form. |
|  7 | nCatLab (categorical)            | same page (clone multiplication / substitution as operad composition) | partial | substitution = clone multiplication | Categorical phrasing exists but is not the relevant generality for an analytic evaluation lemma. |
|  8 | Stacks Project (alg geom)        | "summable power series ring evaluation map ring homomorphism nonarchimedean ... Stacks project" | **n/a** | — | Closest tags (15.39 "results on power series rings", 33.21 complete local rings) are about Noetherian/adic power-series-ring maps, not analytic evaluation at a point of a normed field. Not an algebraic-geometry concept in this form. |
|  9 | MathOverflow / Math.StackExchange| "evaluation of power series at point Banach algebra is ring homomorphism multiplicative nonarchimedean unconditional convergence MathOverflow" | yes (adjacent) | Power series in a Banach algebra evaluate to a **continuous ring morphism** under topological nilpotence; absolutely-convergent / Fréchet-differential treatments | Confirms the fact is textbook-standard for Banach/Banach-algebra analysis (incl. the *Fréchet Differential of a Power Series in Banach Algebras* note); no MO thread treats the lemma as novel — it is folklore. |
| 10 | recent arXiv (last 5 years)      | "formal power series substitution ... convergent" (arXiv hits in #1/#2) | yes | *A Formalization of Divided Powers in Lean* (2507.05327); *Taylor expansions over generalised power series* (2509.08473); *Hyperseries in the non-Archimedean ring of Colombeau generalized numbers* (2006.16141) | Modern formalization/analysis work treats nonarchimedean summable-family products and substitution homomorphisms as standard building blocks — corroborates both the mechanism and the generality. |

**Protocol pass check:** WebSearch ran 4 distinct queries at three generality levels (specific Cauchy-product form, the maximally-general continuous-ring-hom form, named-after/aliases) ✓. ChatGPT MCP unavailable → recorded n/a with reason + compensated ✓. Local refs checked (absent → n/a) ✓. nLab fetched and quoted ✓. nCatLab/Stacks/MathOverflow/arXiv each examined with reasons ✓.

### Literature summary (Phase 3)

Concept identified as: **the multiplicativity of power-series evaluation at a (summable / topologically nilpotent) point** — i.e. *evaluation is a (continuous) ring/algebra homomorphism*. `summable_eval_pow` is the **summability (well-definedness) half** of `eval(Gⁿ) = (eval G)ⁿ`.

Sources agree on the standard form: **yes.** Across Wikipedia, PlanetMath, nLab, and the Banach-algebra literature the canonical statement is: *if `y` is topologically nilpotent (powers → 0) / the evaluation series converges, then `G ↦ ∑ (coeff_n G)·yⁿ` is a continuous ring homomorphism from the power-series ring to the target ring/algebra*; multiplicativity (and hence the `Gⁿ` power law) is an immediate consequence. The nonarchimedean/unconditional-summability specialisation (our setting) is treated via the Cauchy-product-of-summable-families fact (`Summable.mul_of_nonarchimedean`), which is itself in mathlib.

Most general standard form: for a **complete nonarchimedean (Hausdorff) ring/algebra `S`** over `R` and `y ∈ S` such that `Σ (coeff_n f)·yⁿ` converges for every `f` (e.g. `y` topologically nilpotent), evaluation `f ↦ ∑ (coeff_n f)·yⁿ` is a ring/algebra homomorphism `R⟦X⟧ → S`. The `Gⁿ` summability is then `map_pow`/well-definedness.

Generality dimensions where the literature varies:
- **Coefficient/scalar ring**: here `ℚ_[p]` (coeffs) acting on `L`. Literature: any (complete) base ring `R` with target `R`-algebra `S`. The `ℚ_[p]`/`L` split is incidental to this project.
- **Target structure**: here a complete ultrametric normed *field* `L`. Literature: any complete nonarchimedean ring/algebra (the field structure is not used; only `NonarchimedeanRing` + the `Summable` hypothesis are).
- **Convergence regime**: here genuine `Summable` (nonarchimedean unconditional). Literature also covers the absolutely-convergent (archimedean Banach) regime — a *different* regime, which is the one mathlib's `FormalMultilinearSeries.summable_norm_mul_pow` lives in.

Disagreement with the literature: **none.** The Lean form is a faithful (narrow) specialisation of the standard fact.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): evaluation at a summable / topologically-nilpotent point is a ring/algebra homomorphism into **any complete nonarchimedean `R`-algebra `S`**; `summable_eval_pow` is its well-definedness half.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | nonarchimedean normed **field** | any (complete) nonarchimedean **ring/algebra** | **yes** | The proof uses only `NonarchimedeanRing L` (via `Summable.mul_of_nonarchimedean`) + `T3`/topological-semiring (for `summable_sum_mul_antidiagonal_of_summable_mul`). Field structure, the norm, and even completeness are unused (`omit [CompleteSpace L]`). |
| 2 | `[IsUltrametricDist L]` | metric ultrametric | abstract `NonarchimedeanRing` | **yes** | Only the derived `NonarchimedeanRing L` instance is consumed; the *metric* is never touched. State directly over `[NonarchimedeanRing S]` (+ uniform/topological hyps). |
| 3 | coeffs in `ℚ_[p]`, scalars `•` into `L` | `(coeff m G : ℚ_[p]) • yᵐ` over a `ℚ_[p]`-algebra | `(algebraMap R S)(coeff_m G) * yⁿ` for `G : R⟦X⟧`, `S` an `R`-algebra | **yes** | `ℚ_[p]` plays no special role; any base ring `R` with target `R`-algebra `S` works. Mirrors mathlib's `eval₂`/`aeval` shape `φ (coeff d f) * a ^ d`. |
| 4 | `p : ℕ`, `[Fact p.Prime]` | a fixed prime | (absent) | **yes** | Pure dead weight here — `p` enters only through `ℚ_[p]`; the generic statement drops it entirely. |
| 5 | the `Summable` hypothesis `hG` | summable base family | summable base family (or `y` top. nilpotent) | NO (essential) | This is the genuine hypothesis; without it the conclusion is false. It is exactly right. |

### 4b. Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **4** (rows 1–4).

Proposed restatement (literature-standard, mathlib-idiomatic naming):
```lean
variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsUniformAddGroup S] [IsTopologicalRing S] [NonarchimedeanRing S]
  [Algebra R S] [ContinuousSMul R S]

theorem PowerSeries.summable_eval_smul_pow {G : PowerSeries R} {y : S}
    (hG : Summable fun m : ℕ => (PowerSeries.coeff R m G) • y ^ m) (n : ℕ) :
    Summable fun k : ℕ => (PowerSeries.coeff R k (G ^ n)) • y ^ k := by
  sorry  -- proof: the existing induction; mul_of_nonarchimedean already lives at this generality
```
(Equivalently, phrased with `(algebraMap R S) (coeff R m G) * y ^ m` to match mathlib's `eval₂`/`hasSum_eval₂` convention exactly.)

Cost of restatement: **CHEAP–MODERATE** — mechanical. The two load-bearing lemmas already hold at this generality: `Summable.mul_of_nonarchimedean` requires only `[Ring R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]`, and `summable_sum_mul_antidiagonal_of_summable_mul` requires only `[T3Space α] [IsTopologicalSemiring α]`. The induction transcribes verbatim; only the `smul`/`algebraMap` bookkeeping in the `.congr` step needs light adjustment. (Cost does not change the bucket per the skill's cost rule.)

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently; 4c run below.

### 4c. Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let L be a foo" → typeclasses/instances? | **yes** | Replace `[NormedField L][IsUltrametricDist L]` bundle by the single property actually used: `[NonarchimedeanRing S]` (+ topological/uniform hyps). | Applies to *every* complete nonarchimedean ring/algebra, not just normed fields — Tate algebras, `MvPowerSeries`, adic rings. |
| 2 | sequences/metric → filters/topology? | **yes** | The proof already lives in `Summable`/`HasSum` (filter-based) land; just drop the metric `IsUltrametricDist` in favour of the topological `NonarchimedeanRing`. | Unifies with `Summable.mul_of_nonarchimedean`, which is stated topologically; removes the spurious metric dependency. |
| 3 | construct an object → universal-property class? | **yes (the big one)** | This summability fact is the *well-definedness half* of a **`PowerSeries.eval`/`aeval` homomorphism into a complete nonarchimedean (non-linearly-topologized) algebra** — a sibling to mathlib's `PowerSeries.eval₂Hom`/`aeval` that drops `[IsLinearTopology S S]` and instead assumes `[NonarchimedeanRing S]`. The power law `eval(Gⁿ)=(eval G)ⁿ` becomes `map_pow` of that hom. | Would let *all* of `summable_eval_pow`, `tsum_eval_pow`, and the substitution/composition lemmas (`seriesEval`, `tsum_coeff_pow_eq_coeff_subst`) be `map_pow`/`map_mul`/`map_sum` of one homomorphism — and would close a real mathlib gap (see Phase 5). |
| 4 | set-with-closure-pred → bundled substructure? | no | — | No subobject lattice here. |
| 5 | vector-space/metric/field → modules/(semi)ring? | **yes** | `NormedField L` → `NonarchimedeanRing S` (a commutative-ring/algebra weakening); see rows 1–2. | Full module/algebra API; scalar restriction/extension; reuse across NT projects (AdicSpaces' `evalTerm_summable` use the same `mul_of_nonarchimedean` mechanism). |
| 6 | 1-categorical → higher-categorical? | no | — | Not a categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | partial | The antidiagonal Cauchy product generalises to `[HasAntidiagonal A]` (mathlib already provides `summable_sum_mul_antidiagonal_of_summable_mul` at that generality), i.e. to `MvPowerSeries`/`Finsupp`-indexed series. | Aligns with mathlib's existing `HasAntidiagonal` Cauchy-product API; opens the multivariate case. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes.**
- Proposed mathlib-idiomatic restatement: the row-1/2/5 weakening to `PowerSeries.summable_eval_smul_pow` over `[NonarchimedeanRing S]` (the 4b restatement), ideally packaged (row 3) as the well-definedness half of a **nonarchimedean `PowerSeries.eval₂Hom`/`aeval`** that parallels mathlib's linearly-topologized `eval₂Hom` but assumes `NonarchimedeanRing S` instead of `IsLinearTopology S S`.
- Cost: CHEAP–MODERATE for the bare lemma; MODERATE–EXPENSIVE for the full homomorphism packaging (a new file mirroring `PowerSeries/Evaluation.lean`).
- Mathlib downstream this enables: a canonical `PowerSeries.eval`/`aeval` for **normed/Banach nonarchimedean algebras and fields** (the regime mathlib's current `eval₂Hom` *cannot reach* — see Phase 5); `map_pow`/`map_mul`/`map_sum` then subsume this lemma, `tsum_eval_pow`, and the substitution-composition lemmas; reuse by AdicSpaces (`evalTerm_summable`, `mvEvalTerm_summable`) and any p-adic L-function / Tate-algebra evaluation work.
- Real mathematical improvement (not just "looks cooler"): it eliminates a redundancy (the project re-implements, by hand, the well-definedness of an evaluation homomorphism that *should* be a single mathlib `AlgHom`) and fills a genuine hole in mathlib's power-series evaluation API: the **nonarchimedean-but-not-linearly-topologized** target (normed fields) is currently unsupported.

⇒ Phase 4c "modern idiom available" reinforces **YES-but-generalise-first** (the generalise target = the contemporary nonarchimedean-eval form, not merely a typeclass walk).

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths introduced. (Skipped per scope.)

---

### PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.summable_eval_pow`

[A] **Lean-Finder** — n/a: external Lean-Finder service not reachable from this sandboxed environment. Compensated by [D]+[E] over the local mathlib checkout (`.lake/packages/mathlib`, full source) and the WebSearch literature sweep.
[B] **Loogle** — n/a: external Loogle service not reachable here. Type-pattern intent `Summable (fun _ => coeff _ (_ ^ _) • _ ^ _)` covered by [D] grep instead.
[C] **LeanSearch** — n/a: external service not reachable here. Natural-language intent ("evaluation of a power series power is summable / power-series evaluation is multiplicative") covered by [D] grep + the Phase-3 literature.
[D] **Grep mathlib src** — queries: `Summable.*coeff.*\^`, `summable_eval`, `hasSum_pow`, `eval₂.*pow`, `substAlgHom`, `HasEval`, `coeff.*•.*y.*\^.*Summable`, `IsLinearTopology` instances, `FormalMultilinearSeries.*summable_norm_mul_pow`, `Summable.mul_of_nonarchimedean`, `summable_sum_mul_antidiagonal_of_summable_mul`. **Hits — but none matching this form** (see below). 
[E] **Name pattern** — `summable_eval_pow`, `eval_pow`, `summable_eval`, `eval₂Hom`, `aeval` over mathlib: the only `eval`/`aeval` power-series homs are `PowerSeries.eval₂Hom`/`PowerSeries.aeval` (linearly-topologized regime); no `summable_eval`-style lemma exists.

Searched for both:
- the user's current form (`Summable (coeff (G^n) • y^k)` over a normed field) — **not present**;
- the literature-standard form (evaluation-is-a-homomorphism into a complete nonarchimedean algebra) — **present only in the incompatible `IsLinearTopology` regime** (see below).

What mathlib *does* have (the building blocks + the near-miss):
- `Summable.mul_of_nonarchimedean` / `HasSum.mul_of_nonarchimedean` (`Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:125,134`) — product of summable families is summable in a nonarchimedean ring. **The induction's engine.** Stated at full generality (`[Ring R][UniformSpace R][IsUniformAddGroup R][NonarchimedeanRing R]`).
- `summable_sum_mul_antidiagonal_of_summable_mul` (`Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:221`) — antidiagonal Cauchy-sum of a summable product family is summable (`[T3Space α][IsTopologicalSemiring α]`, `[HasAntidiagonal A]`). **The antidiagonal collapse.**
- `PowerSeries.eval₂Hom` / `PowerSeries.aeval` / `PowerSeries.hasSum_eval₂` (`Mathlib/RingTheory/PowerSeries/Evaluation.lean:158,177,211`) — evaluation of a power series at a topologically-nilpotent point **as a `RingHom`/`AlgHom`**, with `hasSum_eval₂` giving `HasSum (fun d => φ (coeff d f) * a^d) (f.eval₂ φ a)`. This is the *exact* homomorphism whose `map_pow` would imply our lemma — **but it requires `[IsLinearTopology S S]`** (`Evaluation.lean:155`).
- `PowerSeries.substAlgHom` (`Mathlib/RingTheory/PowerSeries/Substitution.lean:171`) with `map_pow` (`:201`) — substitution into *another power-series ring* (`MvPowerSeries τ S`); the convergence here is X-adic/coefficient-finiteness (`HasSubst`), **not** analytic `Summable`. Wrong regime.
- `FormalMultilinearSeries.summable_norm_mul_pow` (`Mathlib/Analysis/Analytic/ConvergenceRadius.lean:227`) — summability inside the radius of convergence, via `summable_norm` (**absolutely**-convergent / archimedean regime). The project docstring explicitly works in the *non*-norm-summable nonarchimedean regime, so this is the wrong tool.

**The decisive gap (why mathlib does NOT have our form).** `PowerSeries.eval₂Hom`/`aeval`/`hasSum_eval₂` require `[IsLinearTopology S S]`: `𝓝 (0:S)` must have a basis of `S`-**submodules** (ideals) (`Mathlib/Topology/Algebra/LinearTopology.lean:101–103`). For a nontrivially-normed **field** `L` (our `ℚ_[p]` and its complete ultrametric extensions) the only ideals are `{0}` and `L`, so an ideal-basis of `𝓝 0` would force the **discrete** topology — which `ℚ_[p]` is not. The only mathlib `IsLinearTopology R R` instances are for discrete, adic, ideal-filter, and `MvPowerSeries` topologies (`LinearTopology.lean:161`, `AdicTopology.lean:255`, `IdealFilter/Topology.lean:128`, `MvPowerSeries/LinearTopology.lean`). **None covers a normed field.** Hence mathlib's evaluation-homomorphism machinery cannot be instantiated at `L`, and there is no bridge `Summable (coeff • yⁿ) → HasEval y` for a normed field (grep returned nothing).

Concluded: **not in mathlib** (all five methods exhausted, including the literature-standard form). Mathlib has the *building blocks* (`mul_of_nonarchimedean`, `summable_sum_mul_antidiagonal_of_summable_mul`) and an *incompatible-regime near-miss* (`eval₂Hom` under `IsLinearTopology`, `summable_norm_mul_pow` under absolute convergence), but **not** this nonarchimedean-normed-algebra form.

---

### PHASE 6 — Composition check (+ call sites)

### Call sites — `PadicLFunctions.summable_eval_pow`

Internal use count: **K = 2** (within the project; both in the declaring file `PadicExp.lean`, downstream of the declaration, not counting the declaration head itself).
External-to-file callers: 0 distinct files (the substitution machinery that consumes it lives in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| PadicExp.lean:622 | `summable_eval_pow p G y hG n` — supplies summability of `Gⁿ`-evaluation inside `tsum_eval_pow` (the value half). |
| PadicExp.lean:679 | `(summable_eval_pow p G y hGsum n).tsum_const_smul (coeff n F : ℚ_[p])` — feeds the substitution/composition (`F.subst G`) `tsum` rearrangement. |

Inline-derivation grep (was the equivalent re-derived without using `summable_eval_pow`?): **none found** — no other site re-proves "summability of `Gⁿ`-evaluation" by hand. (Note: the *technique* — `mul_of_nonarchimedean` + antidiagonal — recurs in `MeasureR/FormalPsi.lean:921` and across AdicSpaces, but for *different* statements, not a re-derivation of this lemma.)

Signal reading: K = 2 genuine internal consumers, no inline bypass ⇒ real API, consumers depend on it ⇒ leans toward a **YES-** bucket (consistent with the generality finding). Not dead code; not a wrapper consumers route around.

### Composition check (Phase 6)

Can `summable_eval_pow` be derived from mathlib in ≤3 chained calls?

Attempt 1: `map_pow` of mathlib's `PowerSeries.eval₂Hom`/`aeval` (which would give both summability and the value law for free).
- Mathlib decls used: `PowerSeries.eval₂Hom`, `PowerSeries.hasSum_eval₂`.
- Result: **fails.** Requires `[IsLinearTopology L L]`, which is false for a nontrivially-normed field (Phase 5). Cannot be instantiated at `L`.

Attempt 2: induction using the building blocks (`Summable.mul_of_nonarchimedean`, `summable_sum_mul_antidiagonal_of_summable_mul`, then `.congr` with `coeff_mul`/`Finset.sum_smul`/`smul_mul_smul_comm`/`pow_add`).
- Mathlib decls used: the two summability lemmas above + several rewrite lemmas.
- Result: **fails as a ≤3-call composition.** This is the actual proof: a `Nat` induction with a base case (`summable_of_ne_finset_zero` + `Summable.congr`) and a step that chains `mul_of_nonarchimedean` → `summable_sum_mul_antidiagonal_of_summable_mul` → `.congr` with multi-lemma `rw` reasoning. By the Phase-6 heuristics this is a *proof*, not a composition (multiple `have`s + nontrivial reasoning + `rw [...]` chains).

Conclusion: **NOT-COMPOSABLE.** ⇒ Phase 7 considers the YES verdicts (and Phase 4b/4c push to *YES-but-generalise-first*).

---

## Verdict: `PadicLFunctions.summable_eval_pow`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the statement is the well-definedness half of the classical, textbook "evaluation of a power series at a summable / topologically-nilpotent point is a (continuous) ring homomorphism" (Wikipedia, PlanetMath, nLab "unique adic algebra map", Banach-algebra literature). The maximally-general standard form lives over any complete **nonarchimedean ring/algebra**, not specifically a normed field.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 4 weakenings (normed field → `NonarchimedeanRing`; ultrametric metric → topological nonarchimedean; `ℚ_[p]`/`L` split → arbitrary `R`/`R`-algebra; drop `p`), all CHEAP–MODERATE because the two engine lemmas already hold at full generality. Phase 4c additionally identifies a MODERN-IDIOM target (the nonarchimedean `PowerSeries.eval₂Hom`/`aeval` mathlib lacks).
- Mathlib search (Phase 5): **not in mathlib.** Building blocks present (`Summable.mul_of_nonarchimedean`, `summable_sum_mul_antidiagonal_of_summable_mul`); near-miss `PowerSeries.eval₂Hom`/`hasSum_eval₂` exists but is gated behind `[IsLinearTopology S S]`, which **provably fails for normed fields** (only `{0}`/`L` ideals) — so it cannot yield our form.
- Composition check (Phase 6): **NOT-COMPOSABLE** (the proof is an induction with multi-lemma `rw` reasoning, not a ≤3-call composition); K = 2 genuine internal consumers, no inline re-derivation.

**Rationale (1–2 paragraphs):**

`summable_eval_pow` states a genuine, standard fact mathlib does not currently have *at the right generality*: it is the summability/well-definedness half of "power-series evaluation at a summable point is multiplicative." Mathlib's existing evaluation-homomorphism API (`PowerSeries.eval₂Hom`, `aeval`, `hasSum_eval₂`) would deliver exactly this as `map_pow` — but only over **linearly-topologized** targets (ideal-basis neighborhoods of 0), which excludes precisely the normed/Banach nonarchimedean fields this project (and AdicSpaces, and any p-adic L-function work) cares about. That is why the project re-derives it by hand from `Summable.mul_of_nonarchimedean` + the antidiagonal Cauchy product. The result is real, used (K = 2), and not composable in ≤3 calls — so it is a YES, not a NO.

It is **YES-but-generalise-first** rather than YES-add-as-is because the Lean form is strictly narrower than both the literature standard and the mathlib-idiomatic form. The norm, the ultrametric metric, the field structure, and `ℚ_[p]` itself are all unused; the proof consumes only `NonarchimedeanRing` + topological/uniform hypotheses, and the two engine lemmas already hold at that generality. The right mathlib contribution is the `NonarchimedeanRing`-target restatement (`PowerSeries.summable_eval_smul_pow`), ideally as the well-definedness half of a **nonarchimedean `PowerSeries.eval₂Hom`/`aeval`** paralleling mathlib's linearly-topologized one — which would close the documented `IsLinearTopology` gap and let this lemma, `tsum_eval_pow`, and the substitution-composition lemmas all become `map_pow`/`map_mul`/`map_sum` of a single homomorphism. Per the skill's cost rule, the (modest) regeneralisation cost does not downgrade the verdict.

**Refactor-actionable detail (YES-but-generalise-first):**

Reason for the generalisation: **both** —
- LITERATURE-WEAKENING: Phase 4b found the user's form strictly narrower than the literature-standard nonarchimedean-ring form (4 weakenings).
- MODERN-IDIOM (Bourbaki 2.0): Phase 4c found a contemporary mathlib formulation — a nonarchimedean evaluation homomorphism — that is a real organisational improvement and fills a genuine API gap.

Proposed restatement:
```lean
variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsUniformAddGroup S] [IsTopologicalRing S] [NonarchimedeanRing S]
  [Algebra R S] [ContinuousSMul R S]

/-- If a power series `G : R⟦X⟧` is summably evaluable at `y : S` (a complete
nonarchimedean `R`-algebra), then so is every power `Gⁿ`. -/
theorem PowerSeries.summable_eval_smul_pow {G : PowerSeries R} {y : S}
    (hG : Summable fun m : ℕ => (PowerSeries.coeff R m G) • y ^ m) (n : ℕ) :
    Summable fun k : ℕ => (PowerSeries.coeff R k (G ^ n)) • y ^ k := by
  sorry -- the existing induction; mul_of_nonarchimedean / antidiagonal already at this generality
```
(Optionally state with `(algebraMap R S) (coeff R m G) * y ^ m` to match `hasSum_eval₂`'s convention, and add a `Summable`-hypothesis variant of `hasSum_eval₂` so this becomes well-definedness of a `RingHom`/`AlgHom`.)

Estimated cost of regeneralisation: **CHEAP–MODERATE** (bare lemma); MODERATE–EXPENSIVE if packaged as the full nonarchimedean `eval₂Hom`. EXPENSIVE does not downgrade the verdict.

Mathlib downstream this enables (MODERN-IDIOM, required):
- A canonical evaluation `RingHom`/`AlgHom` `R⟦X⟧ → S` for **normed/Banach nonarchimedean algebras and fields** — the regime mathlib's `PowerSeries.eval₂Hom` cannot reach (blocked by `[IsLinearTopology S S]`).
- `map_pow`/`map_mul`/`map_sum`/`map_add` of that hom would then subsume `summable_eval_pow`, `tsum_eval_pow`, `tsum_coeff_pow_eq_coeff_subst`, and the `seriesEval` substitution lemmas in this file.
- Reuse across AINTLIB: AdicSpaces' `evalTerm_summable`/`mvEvalTerm_summable` (`TateAlgebraWedhorn.lean`, `Wedhorn828.lean`) build the *same* nonarchimedean evaluation by hand and would consume the shared API; ditto `MeasureR/FormalPsi.lean`.
- What the old form blocked: nothing forces summability to come from a homomorphism today, so every consumer threads the `Summable` hypothesis manually — the homomorphism packaging removes that.

Next action: run **`/generalise PadicLFunctions.summable_eval_pow`** (it will tension against both the literature-standard `NonarchimedeanRing` form from Phase 3 and the modern-idiom nonarchimedean-`eval₂Hom` form from Phase 4c) before any mathlib PR. The natural PR grain is to ship it **together with its value-half sibling `tsum_eval_pow`** (and ideally the nonarchimedean `eval₂Hom`/`aeval` packaging) as one `feat(RingTheory/PowerSeries): nonarchimedean evaluation` PR, rather than the lemma alone.

---

## Next step

Run **`/generalise PadicLFunctions.summable_eval_pow`** to restate it over a complete nonarchimedean `R`-algebra `S` (dropping the normed-field / ultrametric-metric / `ℚ_[p]` specialisations), tensioning against both the literature-standard form and the modern-idiom nonarchimedean `PowerSeries.eval₂Hom`/`aeval` (the form mathlib's `IsLinearTopology`-gated `eval₂Hom` cannot reach). Ship it with the value-half sibling `tsum_eval_pow` (and ideally the nonarchimedean evaluation-homomorphism packaging) as a single `feat(RingTheory/PowerSeries)` PR; do not PR the narrow `ℚ_[p]`/normed-field form as-is.
