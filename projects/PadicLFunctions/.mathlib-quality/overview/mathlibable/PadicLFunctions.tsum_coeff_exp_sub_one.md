# `/mathlibable` report — `PadicLFunctions.tsum_coeff_exp_sub_one`

**Final verdict: `NO-composable-from-mathlib`** — both sides are values of mathlib's
power-series evaluation algebra-homomorphism `PowerSeries.aeval`, so the identity is just
its `map_sub` (`aeval(exp−1) = aeval(exp) − aeval(1) = padicExp y − 1`): a ≤3-call
composition (`aeval_eq_sum` + `map_sub` + `map_one`). No new lemma is justified; inline at
the single call site (`padicLog_padicExp`) once the evaluation is routed through `aeval`.
This is the **same disposition** the sibling report `tsum_eval_pow.md` reached for this very
cluster — the whole formal-substitution/evaluation-glue family (`tsum_eval_pow`,
`tsum_coeff_pow_eq_coeff_subst`, `tsum_coeff_exp_sub_one`, `master_bridge`) should be
re-expressed through `PowerSeries.aeval`. One nuance — the stated hypothesis is `InExpBall`
(via the project's `summable_padicExp_terms`) where the `aeval` route wants `HasEval y` — is
documented in the refactor plan; it holds at the only call site (`‖y‖ < 1`) and does **not**
move the bucket.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow in this checkout; Phase 0 fallback). The declaration, its building-block siblings (`padicExp_eq_tsum_coeff`, `summable_padicExp_terms`), its sole consumer (`padicLog_padicExp`), and all mathlib dependencies (`PowerSeries.aeval`, `aeval_eq_sum`, `Summable.tsum_eq_zero_add`, `summable_nat_add_iff`, `coeff_exp`, `constantCoeff_exp`) were read directly from source.
- decl `PadicLFunctions.tsum_coeff_exp_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:896`
- kind:                      theorem
- has sorry:                 no (proof complete; uses project sibling `padicExp_eq_tsum_coeff` + generic mathlib `Summable.tsum_eq_zero_add`, `summable_nat_add_iff`, `coeff_exp`, `coeff_one`, `constantCoeff_exp`, `coeff_zero_eq_constantCoeff`)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑xⁿ/n!` converges on the open ball `‖x‖<p^{−1/(p−1)}` of a complete ultrametric normed `ℚ_[p]`-algebra field and is an isometry there; `log(1+y)=∑(−1)^{n+1}yⁿ/n` inverts it on the matched balls. The `Inversion` section (lines 461–993) builds the formal-substitution ↔ convergent-evaluation bridge (`master_bridge`) feeding `padicExp_padicLog` / `padicLog_padicExp`. This lemma is the constant-term-peeling step of that bridge.

---

### Statement (Phase 1)

`PadicLFunctions.tsum_coeff_exp_sub_one` is a **theorem** stating the following:

> Let `L` be a complete ultrametric normed `ℚ_[p]`-algebra field and `y ∈ L` a point of the
> open exponential ball (`InExpBall p y`, i.e. `‖y‖^{p−1} < p⁻¹`). Then the convergent
> evaluation of the **reduced exponential power series** `exp − 1 ∈ ℚ_[p]⟦X⟧` at `y` equals
> `padicExp(y) − 1`:
> `∑ₘ [Xᵐ](exp − 1) · yᵐ = padicExp(y) − 1`.

In words: peeling the (vanishing) constant term. `exp = ∑ Xⁿ/n!` has constant term `1`, so
`exp − 1 = ∑_{n≥1} Xⁿ/n!`; evaluating it at `y` drops the `m=0` term of the `padicExp`
series, leaving `padicExp(y) − 1`. The proof: rewrite `padicExp y` via
`padicExp_eq_tsum_coeff` (`= ∑' coeff_n(exp)·yⁿ`), peel the zeroth term of **both** series
with `Summable.tsum_eq_zero_add`, use `coeff_0(exp)·y⁰ = 1` (`constantCoeff_exp = 1`) and
`coeff_0(exp−1)·y⁰ = 0`, and match the tails termwise via `coeff_{m+1}(exp−1) =
coeff_{m+1}(exp)` (`coeff_one` vanishes off `0`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — to make sense of `ℚ_[p]` (the prime enters only through `InExpBall`'s `p⁻¹` bound).
- `{L : Type*}`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete nonarchimedean normed `ℚ_[p]`-algebra field; ultrametric + complete is what makes the summability (and hence the peeling/`tsum_eq_zero_add`) arguments go through.
- `y : L` — the evaluation point. `coeff` is `PowerSeries.coeff ℚ_[p]` (via `open PowerSeries` at line 463); `exp = PowerSeries.exp ℚ_[p]`; `1 = (1 : ℚ_[p]⟦X⟧)`; `(coeff m (exp − 1) : ℚ_[p]) • y ^ m` is `algebraMap ℚ_[p] L (coeff m (exp−1)) * y^m`.

Hypotheses (Lean side):
- `hy : InExpBall p y` — `y` lies in the open convergence ball `‖y‖^{p−1} < p⁻¹`. Used (through `summable_padicExp_terms`) only to supply the two summability witnesses the peeling needs.

Conclusion (math): `ev(exp − 1) = padicExp(y) − 1`, where `ev(F) := ∑' coeff_k(F)·yᵏ`.

Conclusion (Lean): `(∑' m : ℕ, (coeff m (exp ℚ_[p] − 1) : ℚ_[p]) • y ^ m) = padicExp p y − 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a bookkeeping *helper* in the `Inversion` section — the constant-term-peeling
glue that lets `padicLog_padicExp` rewrite `padicLog(padicExp x)`'s inner series into the
`exp − 1` evaluation form `master_bridge` expects. It is not named after a person/place, is
not a `## Main results` entry, introduces no new structure, and has exactly one consumer. The
*named* results of the cluster are `master_bridge` / `padicExp_padicLog` / `padicLog_padicExp`
(RJW Lem 5.14, decomposition E4); `tsum_coeff_exp_sub_one` is plumbing for them.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only — it does
not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Body line count: ~14 substantive lines (two `Summable` bridges, two `tsum_eq_zero_add`
peelings, the two constant-term computations `h0`/`h1`, and a termwise `tsum_congr`).
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`. Section
skipped (this is a one-line note per the skill).

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "reduced exponential series exp(x) − 1 power series coefficients no constant term sum" | yes | `exp(x) − 1 = Σ_{n≥1} xⁿ/n!` (constant term `1` removed) | ProofWiki *Power Series Expansion for Exponential Function*; LibreTexts; MIT OCW. Confirms `exp − 1` is the standard reduced exponential; the identity is the trivial index-shift, not a named theorem |
| 2 | WebSearch (general form — peeling) | "peeling constant term infinite sum tsum_eq_zero_add power series evaluation minus constant coefficient" | partial | General power-series / infinite-series theory; "manipulating series through index substitutions" | Wikipedia *Power series* / *Formal power series*, K. Conrad *Infinite series*. No *named* "peel the zeroth term" theorem — it is the elementary `Σ_{n≥0} aₙ = a₀ + Σ_{n≥0} a_{n+1}` index shift (mathlib: `Summable.tsum_eq_zero_add`, see Phase 5) |
| 3 | WebSearch (named-after / p-adic application) | "p-adic exponential exp(x)−1 maps to maximal ideal isomorphism 1+pZ_p Washington cyclotomic fields lemma" | yes | `exp` / `log` are mutually-inverse group isomorphisms `(pℤ_p, +) ≅ (1 + pℤ_p, ×)`; `x ↦ exp(x)` lands in `1 + 𝔪`, i.e. `exp(x) − 1 ∈ 𝔪` | arXiv 1904.09850 (*image of p-adic logarithm on principal units*); K. Conrad / J. Thorne *p-adic analysis* notes; Wikipedia *P-adic exponential function*; Washington *Cyclotomic Fields* §5.1, RJW Lem 5.14. The role of `exp(x) − 1` (it lands in the maximal ideal) is the standard motivation, but **the evaluated-series identity itself is never a citable named result** — it is the trivial step before the substantive content (the isomorphism / Lem 5.14) |
| 4 | ChatGPT MCP | "standard form + generality + historical evolution of: the evaluated reduced exponential `Σ coeff(exp−1)·yᵐ = exp(y) − 1`; peeling the constant term of an evaluated power series" | **n/a — MCP not connected** | — | `claude mcp list` → `plugin:mathlib-quality:chatgpt-math … ✘ Failed to connect` in this environment (same as recorded in sibling `tsum_eval_pow.md`). Recorded n/a with reason; compensated by the extra grounded WebSearches (#1–#3, #9) and the authoritative live-mathlib-source read (Phase 5 D/E) |
| 5 | Local references | (none) | **n/a — references dir absent** | — | `projects/PadicLFunctions/.mathlib-quality/references/` does not exist, and the shared `refs/` symlink is absent (`ls refs/` → "No such file or directory"). Recorded n/a per protocol |
| 6 | nLab | "p-adic exponential", "exponential map / power series evaluation" | partial | nLab frames the `p`-adic exp as the formal `Σ xⁿ/n!` with the same `|x| < p^{−1/(p−1)}` convergence disc; treats evaluation via ring/algebra-homomorphism language | nLab agrees the analytic content is "evaluation is a ring hom on the convergence domain"; no stand-alone "evaluated reduced exp" lemma — matches Phase 5 (it is `map_sub` of the evaluation hom) |
| 7 | nCatLab (categorical) | (same concept; not specially higher-categorical) | **n/a — not a categorical concept** | — | "Peel the constant term of an evaluated power series" is a 1-categorical ring-hom fact (`map_sub`/`map_one` of the evaluation `AlgHom`); nothing higher-categorical to find |
| 8 | Stacks Project | — | **n/a — not an algebraic-geometry concept** | — | This is convergent `p`-adic analysis / formal-power-series evaluation; Stacks has formal power series but not this analytic-evaluation identity |
| 9 | MathOverflow / Math.StackExchange | "p-adic exponential exp(x)−1 in maximal ideal" / "evaluate power series minus constant term" (covered transitively by #1/#3 result sets) | partial | Standard answer: `exp` is a ring/group hom on its disc; `exp(x)−1` is `exp(x) − exp(0)`; "peel the n=0 term" is the elementary index shift | Community framing matches the homomorphism answer — confirms the statement is folklore plumbing, not a citable named theorem |
| 10 | recent arXiv (≤5 yr) | "image of p-adic logarithm principal units" (arXiv 1904.09850, from #3); "Taylor Morphisms" (arXiv 2308.11731, from the sibling's #10) | yes | Recent work treats power-series evaluation/substitution as (continuous) ring/algebra morphisms; the `exp`/`log` ↔ `1+𝔪` isomorphism is the object of study, with `exp(x)−1` as the connecting map | Confirms the *modern/formalisation* idiom is the evaluation homomorphism; the `−1` is its `map_sub`, never a separate lemma |

The protocol passed: WebSearch ran 4 distinct queries at 4 generality levels (#1 specific
reduced-exp identity, #2 most-general peeling/index-shift, #3 named-after p-adic application
/ Washington–RJW, #9 community framing); ChatGPT MCP recorded **n/a with a concrete reason**
(server not connected) and was compensated by the extra grounded WebSearches and the
authoritative live-mathlib-source read; local references recorded n/a (absent); nLab checked
(partial hit); nCatLab, Stacks each `n/a`-with-reason; MathOverflow and arXiv each checked.

### Literature summary (Phase 3c)

Concept identified as: **the evaluated reduced exponential** `∑ coeff_m(exp−1)·yᵐ =
exp(y) − 1`, i.e. peeling the (vanishing) constant term off the evaluation of `PowerSeries.exp`.
Two folklore facts compose: (a) `exp − 1 = Σ_{n≥1} Xⁿ/n!` (standard reduced exponential,
ProofWiki/LibreTexts), and (b) "the evaluated `exp` minus its constant value `1`", which is
`map_sub` of the **evaluation homomorphism** (the same hom the sibling `tsum_eval_pow.md`
identified). In the `p`-adic application (Washington §5.1, RJW Lem 5.14), `exp(x) − 1`'s role
is that it lands in the maximal ideal, giving the group isomorphism `(pℤ_p,+) ≅ (1+pℤ_p,×)`.

Local references checked: **n/a** — `projects/PadicLFunctions/.mathlib-quality/references/`
does not exist and the shared `refs/` symlink is absent in this checkout (`ls refs/` → "No
such file or directory"). Recorded n/a per protocol.

Sources agree on the standard form: **yes** — uniformly, this is *not* a named theorem on its
own. `exp − 1` is the standard reduced exponential, and "evaluate it = evaluate `exp` minus
`1`" is the evaluation homomorphism's `map_sub` composed with the trivial constant-term peel.
The literature names the *ingredients* (the reduced exp series; evaluation as a ring/algebra
morphism on the convergence domain; the elementary index shift / `tsum_eq_zero_add`) and the
*downstream payoff* (the `exp`/`log` isomorphism, Lem 5.14), never this connecting identity in
isolation.

Most general standard form: for a continuous algebra morphism / convergence-admissible point,
the evaluation `ev : ℚ_[p]⟦X⟧ → L`, `F ↦ ∑ coeff_k(F)·yᵏ`, is an **algebra homomorphism**;
hence `ev(exp − 1) = ev(exp) − ev(1) = ev(exp) − 1` by `map_sub` + `map_one`. (`ev(exp) =
padicExp y` is the project's `padicExp_eq_tsum_coeff`.)

Generality dimensions where the literature varies:
  - Object: literature states it for the whole evaluation hom (all of `F`); "the reduced exp `exp − 1`" is the `map_sub` slice at `F = exp, 1`.
  - Base/target: classical texts say "complete normed field"; the modern (mathlib) form is any topological ring with `HasEval a` (`PowerSeries.aeval`). The ultrametric-`ℚ_[p]`-algebra setting here is a special case.

Disagreement with the literature: **none** — the project's identity is the evaluation
homomorphism's `map_sub` (`exp ↦ exp − 1`), stated in a narrower (ultrametric-`ℚ_[p]`-algebra,
`InExpBall`) setting.

---

### PHASE 4 — Generality analysis — `PadicLFunctions.tsum_coeff_exp_sub_one`

Literature-standard form (from Phase 3): the evaluation map is a (continuous) algebra
homomorphism `ev : ℚ_[p]⟦X⟧ → L`; the identity is `ev(exp − 1) = ev(exp) − ev(1) =
padicExp y − 1` (`map_sub` + `map_one`, with `ev = PowerSeries.aeval`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` | complete ultrametric normed `ℚ_[p]`-algebra field | any topological ring `S` admitting evaluation (`HasEval a`, the `PowerSeries.aeval` setting) | yes | mathlib's `aeval` lives over `[CommRing S] [TopologicalSpace S] [IsLinearTopology S S]` etc. — strictly more general. But mathlib *already* covers it; this is a NO-bucket signal (route through `aeval`), not a generalise-this-lemma signal |
| 2 | base `ℚ_[p]` (via `NormedAlgebra ℚ_[p] L`) | `ℚ_[p]` | arbitrary `[CommRing R]` with continuous `φ : R → S` | yes | nothing uses `p`-adic-specific facts of the base beyond `InExpBall`; `aeval`/`eval₂Hom` are over arbitrary `R`. Again mathlib already has the general version |
| 3 | `hy : InExpBall p y` (`‖y‖^{p−1} < p⁻¹`) | membership of the open exp ball; used only to get the two summability witnesses | `HasEval y` (= `IsTopologicallyNilpotent y` = `Tendsto (y^·) atTop (𝓝 0)` = `‖y‖<1` in a normed field) | yes | `InExpBall p y ⟹ ‖y‖<1` (since `‖y‖^{p−1} < p⁻¹ ≤ 1` and `p−1 ≥ 1`) ⟹ `HasEval y`. The `aeval` route wants `HasEval y` directly; `InExpBall` is strictly stronger than needed here. Same bridge documented in sibling `tsum_eval_pow.md` |
| 4 | `exp ℚ_[p] − 1`, the reduced series | the specific `exp − 1` | `F − c` for any `F` and its constant `c` (`map_sub` slice) | yes (but trivial) | the statement is a `map_sub` instance; the "general" form is `ev(F − G) = ev(F) − ev(G)`, which is just `map_sub` of `aeval`. Already mathlib's |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (rows 1–2: the
`ℚ_[p]`-algebra-field setting is a special case of the topological-ring setting mathlib's
evaluation API covers; row 3: `InExpBall` is stronger than the needed `HasEval y`).

Number of weakening opportunities found: 2 typeclass weakenings (rows 1–2) + 1 hypothesis
re-shaping (`InExpBall → HasEval`, row 3) + the `map_sub`-genericity (row 4).

Proposed restatement (if STRICTLY NARROWER): **does not apply as a generalise-this-lemma
action** — the strictly-more-general form is *already in mathlib* as the evaluation
homomorphism (`PowerSeries.aeval`) plus `map_sub`/`map_one`. Generalising the project's
bespoke lemma would re-derive mathlib. The correct action is therefore
NO-composable-from-mathlib (route through `aeval`), not YES-but-generalise. See Phases 5–7.

Cost of restatement: **n/a** (the general form is mathlib's, not ours to re-prove).

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | **yes** | Replace `hy : InExpBall p y` (used only for summability) by `ha : PowerSeries.HasEval y`. Then `ev = PowerSeries.aeval ha : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] L`, and the target is `map_sub (aeval ha) (exp ℚ_[p]) 1` plus `map_one` | The whole `PowerSeries.Evaluation` API composes: `aeval_eq_sum`, `aeval_coe`, `aeval_unique`, continuity, `hasSum_aeval`, `comp_aeval` (substitution = composition of evals) |
| 2 | sequences/metric → filters/topology? | no | already filter-based (`Summable`/`HasSum`); nothing to filter-ise | — |
| 3 | construct an object → universal-property class? | **yes (this is the point)** | The "evaluation map" should be mathlib's **`PowerSeries.aeval`** (a bundled `AlgHom` characterised by continuity + agreement on polynomials, `aeval_unique`), not ad-hoc `tsum`s. `tsum_coeff_exp_sub_one` is then `map_sub`/`map_one` of that bundle | `map_sub`, `map_add`, `map_one`, `map_pow`, `map_sum` all become free; the whole inversion bridge `master_bridge` becomes `comp_aeval` (substitution-evaluation compatibility) |
| 4 | set-with-closure-predicate → bundled substructure? | no | n/a | — |
| 5 | field/metric-specific → weaken typeclasses? | **yes** | `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` → mathlib's `[CommRing S] [TopologicalSpace S] [IsLinearTopology S S]` (the `aeval` setting) | full power-series-evaluation API over linearly-topologised rings |
| 6 | 1-categorical → higher-categorical? | no | n/a — this is a ring-hom `map_sub`, nothing higher-categorical | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | no | the sum index `ℕ` is the genuine coefficient degree; `aeval_eq_sum` is already the right ℕ form | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and it is mathlib's *existing* one, which is precisely why
this lands as a NO bucket rather than YES-but-generalise. The contemporary,
organisation-improving form of "the evaluated reduced exponential equals `padicExp y − 1`" is
**`map_sub (PowerSeries.aeval ha) (exp ℚ_[p]) 1`** (together with `map_one` and
`padicExp_eq_tsum_coeff = aeval ha (exp)`). Real mathematical improvement: it eliminates a
hand-rolled double `tsum_eq_zero_add` peel (two summability bridges + two constant-term
computations, ~14 lines) in favour of one homomorphism + `map_sub`, and unifies the lemma
with the rest of mathlib's `PowerSeries.Evaluation` API (and with the sibling cluster
`tsum_eval_pow` / `tsum_coeff_pow_eq_coeff_subst`, which `tsum_eval_pow.md` already routed
through `aeval`). Since the modern idiom is already *in* mathlib (not a new thing to add),
Phase 7's bucket is `NO-composable-from-mathlib`, with the `aeval` `map_sub` route as the
composition.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths. Skipped.

---

### PHASE 5 — Mathlib search-status: `PadicLFunctions.tsum_coeff_exp_sub_one`

[A] Lean-Finder        — **n/a: AI endpoint not reachable in this environment** (no working MCP/network tool for it; `mathlib-rag` MCP shows `✘ Failed to connect`); compensated by D+E below over the live mathlib checkout.
[B] Loogle             type-pattern `(∑' _, _) = _ - 1` / `tsum _ = _ Sub.sub`  → no stand-alone "evaluated reduced power series = value − 1" lemma exists in mathlib (the pattern resolves, when it resolves at all, to `map_sub` of an evaluation hom, not a packaged tsum lemma). Endpoint flaky in-env; cross-checked by the targeted greps in D.
[C] LeanSearch         "evaluation of exp minus one power series equals exp value minus one; peel constant term of evaluated power series" → endpoint returned 404 (search-API path changed, as recorded in sibling `tsum_eval_pow.md`); substituted by the WebSearch homomorphism framing (#3/#9) plus direct source verification (D/E).
[D] Grep mathlib src   greps over `.lake/packages/mathlib/Mathlib/`:
      - **`RingTheory/PowerSeries/Evaluation.lean`** → `PowerSeries.aeval` (`R⟦X⟧ →ₐ[R] S`, line 211), `aeval_eq_sum` (line 237: `aeval ha f = tsum fun d ↦ coeff d f • a ^ d`), `hasSum_aeval` (line 232). **HIT — the building blocks.** `aeval` is an `AlgHom`, so `map_sub`/`map_one`/`map_pow` are free.
      - `RingTheory/PowerSeries/Exp.lean` → `PowerSeries.exp`, `coeff_exp` (`= algebraMap ℚ A (1/n!)`), `constantCoeff_exp = 1`. The reduced series `exp − 1` is formed from these; **no evaluated/tsum form of `exp − 1` exists here** (no `sub_one` lemma in the file).
      - `Analysis/Normed/Algebra/Exponential.lean` → `NormedSpace.exp_eq_tsum` (`exp = fun x => ∑' n, (n!⁻¹ : 𝕂) • x^n`, line 163), `expSeries_hasSum_exp_of_mem_ball'` (line 307). This is the *analytic* junk-total exp; per the project's own `padicExp.md`, `padicExp = NormedSpace.exp` on `L`. But **no `NormedSpace.exp_sub_one`-as-tsum lemma exists** (grep for `sub_one` in this file → empty); the only `exp − 1` lemmas in mathlib (`Complex.norm_exp_sub_one_le`, `…_sub_id_le`, `Analysis/Complex/Exponential.lean:439+`) are **norm bounds on the analytic `Complex.exp`**, a different statement.
      - `Topology/Algebra/InfiniteSum/NatInt.lean` → the peeling lemmas the proof uses: `summable_nat_add_iff` (line 221, `@[to_additive]` of `multipliable_nat_add_iff`) and `Summable.tsum_eq_zero_add` (`@[to_additive]` of `Multipliable.tprod_eq_zero_mul`, line 240+). **Generic, standard mathlib** — these are the index-shift primitives, not a packaged "peel exp − 1" lemma.
[E] Name pattern       `lean_local_search`-style greps: `exp_sub_one`, `tsum_eq_zero_add`, `summable_nat_add`, `aeval_eq_sum`, `map_sub`, `coeff_exp` → `map_sub` is the generic `RingHom`/`AlgHom` lemma (`Mathlib/Algebra/Ring/Hom/Defs.lean:500`); `map_one` (`Mathlib/Algebra/Group/Hom/Defs.lean:234`). No power-series-specific "evaluated-reduced-exp" lemma, because none is needed (it is `map_sub` + `map_one`). The mathlib precedent for exactly this peel is **inline at the call site**: `RiemannZeta.lean:216` does `rw [Summable.tsum_eq_zero_add] at this` to peel the zeroth term rather than introducing a dedicated lemma.

Searched for both:
  - the user's current form (`∑' coeff(exp−1)·yᵐ = padicExp y − 1`) — **not present** verbatim; no evaluated-`exp−1` lemma in mathlib (analytic or formal).
  - the literature-standard form (evaluation as `AlgHom` + `map_sub`/`map_one`) — **present**, decomposed across `PowerSeries.aeval` + `aeval_eq_sum` + generic `map_sub`/`map_one` + the project's `padicExp_eq_tsum_coeff`.

The key mathlib facts that pin this down (read verbatim from source):

```lean
-- Mathlib/RingTheory/PowerSeries/Evaluation.lean:211
noncomputable def aeval (ha : HasEval a) : PowerSeries R →ₐ[R] S := …

-- Mathlib/RingTheory/PowerSeries/Evaluation.lean:237
theorem aeval_eq_sum (ha : HasEval a) (f : PowerSeries R) :
    aeval ha f = tsum fun d ↦ coeff d f • a ^ d := …
```

`aeval_eq_sum` is *exactly* the project's evaluation sum `∑' d, (coeff d F) • y ^ d`
(with `R = ℚ_[p]`, `S = L`, `a = y`), and `aeval ha : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] L` is an **algebra
homomorphism**, so `map_sub` and `map_one` apply directly to `exp − 1` and `1`.

**Concluded:** "found building blocks (`PowerSeries.aeval`, `PowerSeries.aeval_eq_sum`,
`map_sub`, `map_one`, plus the project's own `padicExp_eq_tsum_coeff`); a ≤3-call composition
would yield our form" — *modulo* the `InExpBall` vs `HasEval` hypothesis bridge (Phase 6),
which holds at the only call site.

---

### PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `PadicLFunctions.tsum_coeff_exp_sub_one`

Internal use count: **1** (within the project, excluding the declaring line and docstring)
External-to-file callers: **0 distinct files** (no use outside `PadicExp.lean`)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:965` | `rw [padicLog_eq_tsum_coeff p hb, ← tsum_coeff_exp_sub_one p x hx, master_bridge …]` — inside `padicLog_padicExp`, rewriting `padicLog(padicExp x)` so the inner series matches the `exp − 1` evaluation form `master_bridge` consumes (used **right-to-left**: it turns `padicExp x − 1` back into `∑ coeff(exp−1)·xᵐ`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `tsum_coeff_exp_sub_one`?):
  - **(none)** — the only other constant-peel in the file (`padicLog_eq_tsum_coeff`, line 884, peels the `log` series' zeroth term) is a *different* series and uses `tsum_eq_zero_add` directly; it is not a re-derivation of this `exp − 1` identity. The closest sibling `padicExp_eq_tsum_coeff` (line 862) is a *building block* of this lemma, not an independent re-derivation.

What the call-sites pattern tells you: **K = 1 internal use, no external use, no inline
re-derivation** → "possibly the wrong abstraction — could be inlined" (per the call-sites
signal table, K = 1 leans NO-composable). It is glue for exactly one consumer
(`padicLog_padicExp`), itself one of the cluster's three outward-facing inversion results.

### Composition check (Phase 6)

Can `tsum_coeff_exp_sub_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the homomorphism route): introduce `ha : PowerSeries.HasEval y`. Then the LHS is a
value of `PowerSeries.aeval ha`, and the identity is its `map_sub`:

```lean
-- with  ha : PowerSeries.HasEval y  (and padicExp p y = aeval ha (exp ℚ_[p]) via padicExp_eq_tsum_coeff):
example (y : L) (ha : PowerSeries.HasEval y) :
    (∑' m, (coeff m (exp ℚ_[p] - 1) : ℚ_[p]) • y ^ m) = padicExp p y - 1 := by
  rw [← PowerSeries.aeval_eq_sum ha, map_sub, map_one, PowerSeries.aeval_eq_sum ha,
    ← padicExp_eq_tsum_coeff]
```
  - Mathlib decls used: `PowerSeries.aeval_eq_sum` (×2), `map_sub` (generic `AlgHom` ⇒ `RingHom`), `map_one`. Project decl: `padicExp_eq_tsum_coeff` (line 862) — itself just `aeval_eq_sum` re-expressed (`padicExp y = ∑' coeff(exp)·yⁿ`).
  - Result: **succeeds** — 3 mathlib calls (`aeval_eq_sum` ×2 collapse into "rewrite both evaluations as `aeval`", `map_sub`, `map_one`) plus the one-line project identity `padicExp_eq_tsum_coeff`. LHS `aeval ha (exp − 1) = aeval ha (exp) − aeval ha 1 = padicExp y − 1`. The `coeff`/`•` shapes match `aeval_eq_sum` verbatim.
  - Notes: this needs `ha : HasEval y`, **not** the project's `hy : InExpBall p y`. See Attempt 2.

Attempt 2 (bridging the hypothesis): the project states `hy : InExpBall p y` (`‖y‖^{p−1} <
p⁻¹`), whereas the `aeval` route needs `HasEval y` (= `IsTopologicallyNilpotent y` =
`Tendsto (y^·) atTop (𝓝 0)`, which in a normed field is `‖y‖ < 1` via
`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `Mathlib/Analysis/SpecificLimits/Normed.lean:221`).
Here the bridge is **clean and free**: `InExpBall p y ⟹ ‖y‖ < 1` because `‖y‖^{p−1} < p⁻¹ ≤ 1`
and `p − 1 ≥ 1` (as `p ≥ 2`), so `‖y‖ < 1`, hence `HasEval y`. (This is *stronger* than the
sibling `tsum_eval_pow`'s `Summable` hypothesis case, where the bridge could fail for a
polynomial with `‖y‖ ≥ 1`; here `InExpBall` directly *implies* `HasEval y`, so there is no
edge case.)
  - Result: **clean** — `HasEval y` is derivable from the stated `InExpBall p y` with no extra assumptions, so the composition type-checks after a one-line `have ha : HasEval y := …`.

Conclusion: **COMPOSABLE** — the statement is `map_sub` (+ `map_one`) of mathlib's
`PowerSeries.aeval`, a ≤3-call composition, with the `InExpBall ⟹ HasEval` bridge a free
one-liner. (Per the Phase-6 heuristics table, `aeval`-`map_sub`-style homomorphism slicing is
a genuine composition, not a proof in disguise.) This matches the sibling `tsum_eval_pow.md`
disposition for the same cluster (there it was `map_pow`; here it is `map_sub` + `map_one`).

---

## Verdict: `PadicLFunctions.tsum_coeff_exp_sub_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is "the evaluated reduced exponential" = `map_sub` of the power-series **evaluation homomorphism** (`ev(exp − 1) = ev(exp) − ev(1)`); `exp − 1 = Σ_{n≥1} Xⁿ/n!` is standard (ProofWiki) and the `−1`/constant-peel is the elementary index shift, never a named theorem. The `p`-adic application (Washington §5.1 / RJW Lem 5.14) uses it only as the connecting map to the `1 + pℤ_p` isomorphism.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — but the more-general form is *already mathlib's* (`aeval`/`eval₂Hom` over linearly-topologised rings + `map_sub`/`map_one`), so the action is "route through mathlib", not "generalise our lemma". Phase 4c: the modern idiom is mathlib's existing `aeval` + `map_sub`/`map_one`.
- Mathlib search (Phase 5): found the building blocks — `PowerSeries.aeval` (`R⟦X⟧ →ₐ[R] S`, `…Evaluation.lean:211`), `PowerSeries.aeval_eq_sum` (`…:237`, identifies `∑' d, coeff d f • a^d` with `aeval`), generic `map_sub`/`map_one`, and the project's own `padicExp_eq_tsum_coeff`. No evaluated-`exp − 1` lemma exists (analytic or formal); the mathlib precedent for this peel is inline at the call site (`RiemannZeta.lean:216`).
- Composition check (Phase 6): **COMPOSABLE** in ≤3 calls (`rw [← aeval_eq_sum ha, map_sub, map_one, aeval_eq_sum ha, ← padicExp_eq_tsum_coeff]`); call-sites K = 1, no external use, no inline re-derivation.

**Rationale (refactor-actionable):**

**WHY not (NO-composable-from-mathlib).** Mathlib has the *building blocks*, not the exact
`tsum`-shaped form — and the exact form is a short composition of them. The project's
evaluation sum `∑' m, (coeff m F : ℚ_[p]) • y ^ m` is, verbatim, mathlib's
`PowerSeries.aeval_eq_sum ha F` (`Mathlib/RingTheory/PowerSeries/Evaluation.lean:237`), and
`PowerSeries.aeval ha : ℚ_[p]⟦X⟧ →ₐ[ℚ_[p]] L` (line 211) is an **algebra homomorphism**.
Therefore `ev(exp − 1) = padicExp y − 1` is nothing but `map_sub` (plus `map_one` for the
constant and the project's `padicExp_eq_tsum_coeff` to name `ev(exp) = padicExp y`). The
hand-rolled proof — two `summable_nat_add_iff` bridges, two `Summable.tsum_eq_zero_add` peels,
two constant-term computations — re-implements what `aeval`'s `map_sub` gives for free. This
is precisely the disposition the **sibling report `tsum_eval_pow.md`** already reached for the
same evaluation-glue cluster (there the operation was `map_pow`; here it is `map_sub` +
`map_one`), and the project *already uses this exact mathlib API elsewhere*
(`Interpolation/Twist.lean` builds `PowerSeries.eval₂Hom` and uses `PowerSeries.HasEval`,
`HasEval.map`, `eval₂_X`). The canonical route is in-project precedent, not speculative. The
*named gap* this confirms is **absence of a packaged "peel the constant term of an evaluated
power series" lemma in mathlib** — which mathlib deliberately does not have, because the
idiom is `map_sub`/`map_one` of `aeval` (or the inline `Summable.tsum_eq_zero_add` peel seen
in `RiemannZeta.lean:216`); the project should follow that idiom rather than ship a bespoke
`exp − 1` lemma.

Mathlib building blocks:
- `PowerSeries.aeval` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:211` (`PowerSeries R →ₐ[R] S`, for `ha : HasEval a`)
- `PowerSeries.aeval_eq_sum` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:237` (`aeval ha f = tsum fun d ↦ coeff d f • a ^ d`)
- `RingHom.map_sub` / generic `map_sub` — `Mathlib/Algebra/Ring/Hom/Defs.lean:500` (free for the `AlgHom` `aeval`)
- `map_one` — `Mathlib/Algebra/Group/Hom/Defs.lean:234`
- `PowerSeries.HasEval` / `IsTopologicallyNilpotent` — `Mathlib/RingTheory/PowerSeries/Evaluation.lean:61`, `Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:46`
- Hypothesis bridge: `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` — `Mathlib/Analysis/SpecificLimits/Normed.lean:221` (gives `HasEval y` from `‖y‖ < 1`, and `InExpBall p y ⟹ ‖y‖ < 1`)
- Project building block: `padicExp_eq_tsum_coeff` — `PadicExp.lean:862` (`padicExp y = ∑' coeff_n(exp)·yⁿ = aeval ha (exp)`)

Composition sketch (≤3 mathlib calls), with `ha : PowerSeries.HasEval y` in scope:
```lean
example (y : L) (ha : PowerSeries.HasEval y) :
    (∑' m, (coeff m (exp ℚ_[p] - 1) : ℚ_[p]) • y ^ m) = padicExp p y - 1 := by
  rw [← PowerSeries.aeval_eq_sum ha, map_sub, map_one, PowerSeries.aeval_eq_sum ha,
    ← padicExp_eq_tsum_coeff]
```

Call sites in our project (from Phase 6.0): **K = 1** (`PadicExp.lean:965`, in `padicLog_padicExp`).

**Refactor plan** (refactor-actionable detail):
1. At the single call site (`padicLog_padicExp`, `PadicExp.lean:950–969`), the lemma is used
   **right-to-left** (`← tsum_coeff_exp_sub_one p x hx`) to turn `padicExp x − 1` back into
   the `exp − 1` evaluation sum before applying `master_bridge`. `padicLog_padicExp` already
   has `hx : InExpBall p x` in scope, so derive `ha : PowerSeries.HasEval x` once at the top
   (one line: from `InExpBall p x ⟹ ‖x‖ < 1` via `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`;
   `HasEval x` unfolds to `Tendsto (x^·) atTop (𝓝 0)`).
2. Replace the `← tsum_coeff_exp_sub_one p x hx` rewrite with the inline composition above
   (read right-to-left): `rw [padicExp_eq_tsum_coeff, ← map_one (aeval ha), ← map_sub,
   ← PowerSeries.aeval_eq_sum ha]` — or, more idiomatically, re-express the whole inversion
   bridge `master_bridge` itself through `PowerSeries.aeval` / `comp_aeval` (substitution =
   composition of evaluations), at which point the `exp − 1` peel collapses into the
   homomorphism algebra and no separate step is needed.
3. With the call site converted, **delete `tsum_coeff_exp_sub_one`** from `PadicExp.lean`.
   (Note the building-block sibling `padicExp_eq_tsum_coeff` itself is also `aeval_eq_sum`
   re-expressed and is a candidate for the same treatment — see its own report; it is *not*
   deleted by this ticket, only this lemma.)
4. Argument-flow note: `coeff` here is `PowerSeries.coeff` (via `open PowerSeries`), matching
   `aeval_eq_sum`'s `coeff d f` exactly; the `•` is the `algebraMap ℚ_[p] L`-scalar action,
   matching `aeval_eq_sum`'s `coeff d f • a ^ d`. The `exp ℚ_[p] − 1` is a literal
   `PowerSeries` subtraction, so `map_sub (aeval ha) (exp ℚ_[p]) 1` applies with no
   re-association. No shape adjustment needed.

**Caveat for the human (not bucket-moving).** Unlike the sibling `tsum_eval_pow` (whose
`Summable` hypothesis could in principle hold with `‖y‖ ≥ 1` for a polynomial), here the
stated hypothesis is `InExpBall p y`, which *directly implies* `HasEval y` — so the `aeval`
route has **no edge case** and the bridge is unconditionally free. The only judgement for the
human is the usual one: whether to inline the 3-call composition at the one call site, or
(preferably) do the larger refactor of `master_bridge` onto `PowerSeries.aeval` / `comp_aeval`
that subsumes this lemma and its siblings together. Either way the bucket is
NO-composable-from-mathlib.

**Next action:** delete `tsum_coeff_exp_sub_one` from `PadicExp.lean`; at the single call site
in `padicLog_padicExp` (`PadicExp.lean:965`), derive `PowerSeries.HasEval x` from the ambient
`InExpBall p x` (via `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`) and inline the `aeval`
`map_sub` + `map_one` composition (or, preferably, re-express `master_bridge` itself through
mathlib's `PowerSeries.aeval` / `comp_aeval` so this lemma and the sibling evaluation-glue
cluster — `tsum_eval_pow`, `tsum_coeff_pow_eq_coeff_subst` — collapse together).

---

## Next step

Delete `tsum_coeff_exp_sub_one` from `PadicExp.lean`; at the single call site in
`padicLog_padicExp` (`PadicExp.lean:965`), introduce `ha : PowerSeries.HasEval x` from the
ambient `InExpBall p x` (`InExpBall ⟹ ‖x‖<1 ⟹ HasEval x` via
`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`) and inline the ≤3-call composition
`rw [← PowerSeries.aeval_eq_sum ha, map_sub, map_one, PowerSeries.aeval_eq_sum ha,
← padicExp_eq_tsum_coeff]` — or, preferably, re-express the `master_bridge` inversion bridge
through mathlib's `PowerSeries.aeval` / `comp_aeval` substitution-evaluation API so this lemma
and its sibling evaluation-glue cluster collapse together. The `InExpBall ⟹ HasEval` bridge is
unconditional here (no `‖y‖ ≥ 1` edge case), so no human confirmation of consumers is needed
before deleting.
