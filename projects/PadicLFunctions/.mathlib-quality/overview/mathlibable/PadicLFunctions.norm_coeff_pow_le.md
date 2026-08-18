# `/mathlibable` report — `PadicLFunctions.norm_coeff_pow_le`

**Final verdict: `BORDERLINE-needs-human`**

---

## Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — build is stale/slow here; read the decl + deps directly).
- decl `PadicLFunctions.norm_coeff_pow_le`: resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:742`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The p-adic exponential `exp(x)=∑xⁿ/n!` and logarithm — convergence on the ball `‖x‖<p^{−1/(p−1)}`, isometry, and `xˢ := exp(s·log x)` (RJW Lemma 5.14, citing Cassels §12 / Washington §5.1).

---

## Statement (Phase 1)

`norm_coeff_pow_le` is a theorem stating the following.

Let `G ∈ ℚ_[p]⟦X⟧` be a formal power series with zero constant term (`[X⁰]G = 0`), whose coefficients obey the Legendre-type decay bound `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` for every `j ≥ 1`. Then for all `n, k ∈ ℕ`, the `k`-th coefficient of the `n`-th power `Gⁿ` obeys the analogous shifted bound

  ‖[Xᵏ](Gⁿ)‖^{p−1} ≤ p^{k−n}.

Mathematically this is the additive-valuation statement `v_p([Xᵏ](Gⁿ)) ≥ (k−n)/(p−1)` — i.e. the order of `Gⁿ` is `≥ n` (each factor contributes order `≥ 1`) and the valuation telescopes along the multinomial expansion. The `(p−1)`-th power on the norm and the integer exponent `p^{k−n}` are a deliberate **rpow-free encoding** of the half-integer p-adic valuations; the whole `PadicExp.lean` file is written this way to stay inside `zpow`/`Nat.pow` and avoid `Real.rpow`.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the prime; `ℚ_[p]` is the p-adic numbers.
- `(G : PowerSeries ℚ_[p])` — a univariate formal power series over `ℚ_[p]`.
- (file-level `{L}` normed-algebra variables are present but **not used** by this theorem — it is stated purely over `ℚ_[p]`.)

Hypotheses (Lean side):
- `(hcoeff : ∀ j, 1 ≤ j → ‖(coeff j G : ℚ_[p])‖ ^ (p−1) ≤ (p:ℝ) ^ (j−1))` — termwise Legendre decay of `G`'s coefficients.
- `(hc0 : (coeff 0 G : ℚ_[p]) = 0)` — zero constant term.
- `(n k : ℕ)` — the power and the coefficient index.

Conclusion (math): `‖[Xᵏ](Gⁿ)‖^{p−1} ≤ p^{k−n}`.

Conclusion (Lean): `‖(coeff k (G ^ n) : ℚ_[p])‖ ^ (p − 1) ≤ (p : ℝ) ^ (k − n)`.

**Proof body (2 lines):** `rw [coeff_pow]` (mathlib `PowerSeries.coeff_pow`: `[Xᵏ](Gⁿ) = ∑_{l ∈ finsuppAntidiag (range n) k} ∏_{i} [X^{lᵢ}]G`) then `pow_norm_sum_le` (project ultrametric sum-power bound) reducing the goal to the per-tuple bound `norm_coeff_prod_le p G hcoeff hc0 n k l hl`. So it is a thin wrapper around the genuine work in `norm_coeff_prod_le` (the Legendre telescoping `∑(lᵢ−1) = k−n`) and `pow_norm_sum_le` (the ultrametric reduction of a sum-norm to the max term-norm).

---

## Size classification (Phase 2a)

Verdict: SMALL
Reason: It is a helper estimate (one of cluster R5.E in the decomposition), not a `## Main results` entry and not named after a person/place. It feeds exactly one downstream lemma (`summable_prod_family`). It is the "power" companion of `norm_coeff_prod_le` (the per-tuple case), itself a sub-step.

(Literature width was EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (No one-liner / defeq / diamond concern; Phase 4.5 is also skipped for the same reason.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic power series coefficient valuation bound power of series Legendre formula factorial"            | partial | Legendre `v_p(n!)=(n−s_p(n))/(p−1)`; convergence of p-adic series via coeff valuations | The *ingredients* (Legendre, `‖aₙxⁿ‖→0`) are standard; no source isolates the `‖[Xᵏ](Gⁿ)‖` bound as a named lemma. Eremin arXiv:1907.11902; Conrad p-adic infinite series notes. |
|  2 | WebSearch (general form)         | "valuation of coefficients of powers of a power series p-adic exponential convergence ball nonarchimedean" | partial | exp radius `p^{−1/(p−1)}`; convergence ⇔ `‖aₙ‖Rⁿ→0` | Confirms the *purpose* (well-definedness of exp). The coefficient-of-power bound is a step inside that proof, not a stand-alone named result. |
|  3 | WebSearch (named-after / aliases / general framework) | "Gauss norm power series ultrametric submultiplicative coefficients of n-th power bound non-archimedean" | YES  | **Gauss norm** `‖∑fᵢXⁱ‖_c = sup_i ‖fᵢ‖cⁱ`; submultiplicative `‖fg‖≤‖f‖‖g‖`, multiplicative on `K⟪X⟫` | **This is the standard framework.** The target = a Gauss-norm power bound `‖Gⁿ‖_c ≤ ‖G‖_cⁿ` re-encoded coefficientwise + rpow-free. Top hit was mathlib's own `RingTheory.PowerSeries.GaussNorm` (feeds Phase 5). |
|  4 | WebSearch (framework, standard theorem) | "\"Gauss norm\" multiplicative power series valuation coefficient product nonarchimedean field standard theorem" | YES | Gauss valuation `\|∑fᵢXⁱ\|_a = max_i \|a\|ⁱ\|fᵢ\|`; Tate-algebra norm `‖f₁f₂‖≤‖f₁‖‖f₂‖`, Maximum Principle | Achinger / Conrad "Gauss norm and Gauss's lemma" / B. Conrad AWS notes — the submultiplicative Gauss/Tate norm is the canonical home of "norm of coeff of a product/power". |
|  5 | ChatGPT MCP                      | n/a                                                                                                    | n/a  | —                                | ChatGPT MCP is **not configured** in this repo (no `.mcp.json`, no chatgpt entry in settings). Recorded n/a per the protocol's "or recorded n/a with reason" clause; compensated by running 4 distinct WebSearch passes + 2 fetches + nLab + arXiv + Conrad PDF. |
|  6 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (no references dir)              | Directory absent; no `refs/` symlink. Recorded n/a. (The file's own docstring already cites the human sources: Cassels §12, Washington §5.1, RJW Lem 5.14.) |
|  7 | nLab                             | https://ncatlab.org/nlab/show/Gauss+norm                                                               | n/a  | (404 — no dedicated nLab page)   | nLab has no "Gauss norm" page; the concept lives under non-archimedean/rigid geometry. Not a categorical concept, so nLab adds nothing beyond channels 3–4. |
|  8 | nCatLab / Stacks Project         | (Gauss/Tate norm of power series)                                                                      | n/a  | —                                | n/a — not an algebraic-geometry-scheme or higher-categorical concept; it is elementary non-archimedean analysis. Stacks covers valuations abstractly but not this coefficient estimate. |
|  9 | MathOverflow / Math.StackExchange | "p-adic valuation coefficient of n-th power of power series … exponential well-defined"                 | partial | Reconfirms Legendre + Kummer for coefficient valuations | No MO/SE thread states this exact lemma; consistent with it being a routine internal step. |
| 10 | recent arXiv (last 5 yrs) + Conrad PDF | "composition substitution power series order coeff bound p-adic exponential isometry disc 2024"; fetched Conrad `infseriespadic.pdf` | partial | exp radius `p^{−1/(p−1)}`; "isometric isomorphism on small discs"; Dwork exponential | arXiv:2509.26295, 2404.05177, 1809.07705. The coefficient bound for `Gⁿ` is used implicitly in such convergence/isometry arguments but never extracted as a citable named theorem. |

### Literature summary (Phase 3)

Concept identified as: an instance of **Gauss-norm (equivalently Tate-algebra norm) submultiplicativity for powers**, `‖Gⁿ‖_c ≤ ‖G‖_cⁿ`, specialised to `ℚ_[p]` at the critical exponential radius and re-encoded rpow-free via the `(p−1)`-power; the underlying valuation fact is **Legendre's formula** through `norm_coeff_prod_le`. The result also packages `order(Gⁿ) ≥ n` (from `[X⁰]G=0`).

Sources agree on the standard form: yes (for the *framework*) — the Gauss/Tate norm is submultiplicative and indeed multiplicative on `K⟪X⟫` over a non-archimedean field (Conrad, Achinger, B. Conrad AWS; mathlib `Polynomial.gaussNorm_mul`). No source states this *specific* coefficientwise rpow-free p-adic inequality as a named lemma — it is an internal estimate in p-adic-exponential well-definedness proofs (Cassels §12, Washington §5.1, Conrad's p-adic series notes).

Most general standard form (prose): for a non-archimedean field `K`, the Gauss norm `‖∑fᵢXⁱ‖_c = sup_i ‖fᵢ‖cⁱ` is submultiplicative, so `‖fg‖_c ≤ ‖f‖_c‖g‖_c` and by induction `‖fⁿ‖_c ≤ ‖f‖_cⁿ`; combined with `order(fⁿ) ≥ n·order(f)` this yields per-coefficient bounds of exactly the shape proved here.

Generality dimensions where the literature varies:
  - Base field: the literature states it for any non-archimedean (complete) field `K`; the target fixes `K = ℚ_[p]`.
  - Norm encoding: the literature uses the real-valued Gauss norm at a radius `c` (involving `Real.rpow` at the critical p-adic radius); the target uses an rpow-free `‖·‖^{p−1} ≤ p^{integer}` encoding.
  - Multiplicative vs submultiplicative: over `K⟪X⟫` the Gauss norm is *multiplicative* (`gaussNorm_mul`); the target only needs the `≤` (submultiplicative + order) direction.

Disagreement with the literature: none. The target is a faithful, deliberately specialised + rpow-free instance of the standard submultiplicative Gauss-norm bound for powers.

---

## Generality analysis — `PadicLFunctions.norm_coeff_pow_le` (Phase 4)

Literature-standard form (from Phase 3): Gauss-norm submultiplicativity for powers over a non-archimedean field, `‖fⁿ‖_c ≤ ‖f‖_cⁿ`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | base ring | `ℚ_[p]` (p-adics) | any non-archimedean field `K` / ultrametric normed comm. ring | yes | Both the hypothesis and conclusion are pure norm inequalities; `coeff_pow` + the ultrametric sum bound work over any `IsUltrametricDist` normed comm. ring. `ℚ_[p]` is used only to give `p` and the `p^{·}` constants their meaning, not in the proof mechanics. |
| 2 | norm encoding `‖·‖^{p−1} ≤ p^{j−1}` | rpow-free integer-power form, anchored at the prime `p` and exponent `p−1` | real Gauss norm `‖f‖_c` at radius `c=p^{−1/(p−1)}` (uses `Real.rpow`) | yes (the general form is the Gauss-norm one) | The `(p−1)`-power / `p^{integer}` form is an encoding choice to avoid `Real.rpow`; the literature-standard form is the cleaner real Gauss-norm statement. Reformulating loses the rpow-free property the project deliberately maintains. |
| 3 | `hc0 : coeff 0 G = 0` | constant term zero | `order(f) ≥ 1`, giving `order(fⁿ) ≥ n` | partially | Needed for the `k−n` (vs `k`) shift; the general Gauss-norm bound `‖Gⁿ‖_c ≤ ‖G‖_cⁿ` does not need it, but the *shifted exponent* `p^{k−n}` does. So it is essential to this exact conclusion. mathlib already has `le_order_pow_of_constantCoeff_eq_zero` for the order half. |
| 4 | `n k : ℕ` | natural power & index | same | NO | Intrinsic to the statement. |

### 4b. Generality verdict

The current form is: STRICTLY NARROWER THAN STANDARD
Number of weakening opportunities found: 2 (base ring `ℚ_[p] → ` ultrametric normed comm. ring; rpow-free encoding `→` real Gauss norm).
Proposed restatement (general): the literature-standard target is **not** a small tweak of this signature — it is `PowerSeries.gaussNorm_pow_le : gaussNorm v c (f^n) ≤ (gaussNorm v c f)^n` (currently absent from mathlib; see Phase 5), from which this p-adic, rpow-free, order-shifted corollary would be *derived*, not *replaced*.
Cost of restatement: MODERATE — proving `gaussNorm_pow_le` from the existing `gaussNorm_mul_le` is an easy induction, but then *re-deriving the present rpow-free `‖·‖^{p−1} ≤ p^{k−n}` corollary from it* requires moving through `Real.rpow` at the critical radius and back, which the project deliberately avoids. (Cost does NOT downgrade the verdict; it informs sequencing.)

### 4c. Modern-idiom check — Bourbaki 2.0 (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already fully typeclass-driven (`Fact p.Prime`, normed-field instances) | — |
| 2 | sequences/metric → filters/topological? | no | it is a finite per-coefficient inequality; no limit to filter-ise (the limit lives downstream in `summable_prod_family`) | — |
| 3 | construct an object → universal-property class? | no | it is a proposition, not a construction | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | no substructure here | — |
| 5 | field/metric-specific → weaken to module / (semi)ring / ultrametric? | **YES** | state over an ultrametric normed comm. ring; better still, route through mathlib's **`PowerSeries.gaussNorm`** so the bound becomes `gaussNorm (f^n) ≤ (gaussNorm f)^n` (an inductive corollary of `gaussNorm_mul_le`) | unifies with all of `RingTheory/{PowerSeries,Polynomial,MvPowerSeries}/GaussNorm.lean`; the Tate-algebra / `IsRestricted` ecosystem; `gaussNorm_isAbsoluteValue` |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | `n,k : ℕ` are intrinsic | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes.
- Proposed mathlib-idiomatic restatement: **`PowerSeries.gaussNorm_pow_le`** — `gaussNorm v c (f ^ n) ≤ (gaussNorm v c f) ^ n` for a non-archimedean `v` with `f` having `HasGaussNorm`, proved by induction from the existing `MvPowerSeries.gaussNorm_mul_le`. The present theorem would then be a p-adic, rpow-free, order-shifted *corollary*.
- Cost: MODERATE (the general `gaussNorm_pow_le` is CHEAP; re-deriving the rpow-free order-shifted form on top is MODERATE).
- Mathlib downstream this enables: closes a real gap — mathlib's Gauss-norm API has `gaussNorm_mul`/`gaussNorm_mul_le` (binary) but **no power version**; a `gaussNorm_pow_le` would be the natural, reusable lemma. It composes with `gaussNorm_isAbsoluteValue`, the Tate-algebra `IsRestricted.mul`, and any future analytic-`K⟪X⟫` development.
- Real mathematical improvement: the project's bare coefficient inequality re-proves (in disguise, via `coeff_pow` + `pow_norm_sum_le`) a special case of Gauss-norm power-submultiplicativity that *should* be a general lemma; extracting `gaussNorm_pow_le` removes that redundancy library-wide.

Because Phase 4b is STRICTLY NARROWER **and** Phase 4c finds a real modern-idiom target (`gaussNorm_pow_le`), the YES path, if taken, would be `YES-but-generalise-first`, not `YES-add-as-is`. But see Phase 7 — the single internal consumer + the rpow-free-vs-Gauss-norm tension make the *whether-to-upstream-at-all* question a human call.

---

## Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

## Mathlib search-status: `PadicLFunctions.norm_coeff_pow_le` (Phase 5)

[A] Lean-Finder       n/a — Lean-Finder MCP not available in this environment. Compensated by [D]+[E] grep over the local mathlib checkout (`.lake/packages/mathlib/`) + the literature framework name from Phase 3.
[B] Loogle            type pattern `⊢ ‖coeff _ (_ ^ _)‖ ^ _ ≤ _ ^ _` / `gaussNorm _ _ (_ ^ _) ≤ _`  — n/a (no live Loogle here); emulated structurally via grep below.
[C] LeanSearch        "norm of coefficient of a power of a power series is bounded"; "Gauss norm of a power is bounded" — n/a (no live LeanSearch); covered by the WebSearch hits in Phase 3 (#3/#4 surfaced mathlib's GaussNorm files directly).
[D] Grep mathlib src  `gaussNorm_pow`, `gaussNorm.*\^.*le`, `coeff_pow.*le`, `norm_coeff.*pow`, `order_pow`, `le_order_pow`, `IsRestricted`, all `*GaussNorm.lean` decl heads — see results below.
[E] Name pattern      `norm_coeff`, `gaussNorm_mul`, `gaussNorm_add_le_max`, `le_order_pow_of_constantCoeff_eq_zero`, `IsRestricted.mul` — see below.

Building blocks found in mathlib (all confirmed by reading the source):
- `PowerSeries.coeff_pow (k n : ℕ) (φ)` (`RingTheory/PowerSeries/Basic.lean:631`) — `coeff n (φ^k) = ∑_{l ∈ finsuppAntidiag (range k) n} ∏_i coeff (l i) φ`. **This is the project proof's first line.**
- `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` — the ultrametric `‖∑‖ ≤ max` bound (used inside the project's `pow_norm_sum_le`).
- `PowerSeries.le_order_pow_of_constantCoeff_eq_zero (n) (hf : constantCoeff φ = 0)` (`RingTheory/PowerSeries/Order.lean:231`) and `order_pow` (`:444`) — the `order(Gⁿ) ≥ n` half.
- `MvPowerSeries.gaussNorm_mul_le` (`RingTheory/MvPowerSeries/GaussNorm.lean:132`) — `gaussNorm v c (f*g) ≤ gaussNorm v c f * gaussNorm v c g`, for a non-archimedean sub-multiplicative `v` with `HasGaussNorm` on both factors.
- `Polynomial.gaussNorm_mul` / `gaussNorm_mul_le` / `gaussNorm_isAbsoluteValue` (`RingTheory/Polynomial/GaussNorm.lean:274/195/281`) — full multiplicativity for polynomials (abs-value `v`).
- `PowerSeries.gaussNorm_add_le_max` (`RingTheory/PowerSeries/GaussNorm.lean:102`) and `le_gaussNorm`, `gaussNorm_nonneg`, `gaussNorm_eq` — the univariate Gauss-norm API.
- `PowerSeries.IsRestricted` + `IsRestricted.mul`/`.add` (`RingTheory/PowerSeries/Restricted.lean:32,118,65`) — the Tate-algebra closure under product, but only at the *uniform* `‖coeff n f‖·|c|ⁿ ≤ 1` level (no quantitative `p^{k−n}` decay).

Searched for both:
  - the user's current form (`‖coeff k (G^n)‖^{p−1} ≤ p^{k−n}`) → **no hit**: no `norm_coeff_pow_le`-shaped lemma anywhere in mathlib.
  - the literature-standard form (Gauss-norm power bound `gaussNorm (f^n) ≤ (gaussNorm f)^n`) → **no hit**: mathlib has `gaussNorm_mul`/`gaussNorm_mul_le` (binary) and `gaussNorm_add_le_max`, but **no `gaussNorm_pow_le`** (grep for `gaussNorm_pow` returns nothing). The power version is a genuine API gap.

Concluded: **not in mathlib (all available methods exhausted, plus the literature-standard Gauss-norm form).** Mathlib has the *binary* and *building-block* pieces but neither this exact rpow-free p-adic coefficient bound nor its general parent `gaussNorm_pow_le`.

---

## Call sites — `PadicLFunctions.norm_coeff_pow_le` (Phase 6.0)

Internal use count: **K = 1** (within the project, excluding the declaring file's own siblings — actually the single use is *inside the same file*).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:808 | `mul_le_mul (hF x.1 h1n) (norm_coeff_pow_le p G hGc hGc0 x.1 x.2) (by positivity) (by positivity)` — inside `summable_prod_family`, bounding `‖[X^{x.1}]F · [X^{x.2}](G^{x.1})‖^{p−1}`. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_coeff_pow_le`?):
  - **(none directly).** Note: `ResidueZeta.norm_coeff_pow_le_one` and `GaloisAction.norm_coeff_pow_le_one'` are **different lemmas** (a `≤ 1` Tate-algebra bound on `coeff k (G^n)`, not the `≤ p^{k−n}` decay bound), each proved independently in their own files. They are a *naming* near-collision, not a re-derivation of this theorem. They suggest a related (but distinct) "norm of coeff of a power" pattern recurs across the project, which strengthens the case that the *general* engine belongs in a shared/mathlib location.

### Composition check (Phase 6)

Can `norm_coeff_pow_le` be derived from mathlib in ≤3 chained calls?

Attempt 1 — direct mathlib composition: `rw [coeff_pow]` then bound the sum.
  - Mathlib decls used: `PowerSeries.coeff_pow`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.
  - Result: **partial.** After `coeff_pow` the goal is `‖∑_l ∏_i coeff (lᵢ) G‖^{p−1} ≤ p^{k−n}`. Reducing the sum-norm to the max term-norm needs `pow_norm_sum_le` — a *project* lemma (3+ lines: empty-set case + `Finset.exists_mem_eq_sup'` + the ultrametric bound), not a single mathlib call. Then each term needs `norm_coeff_prod_le` — a *project* lemma whose own proof is ~25 lines (antidiagonal split, `zero_pow` for any `lᵢ=0`, `Finset.prod_le_prod`, and the Legendre telescoping `∑(lᵢ−1) = k−n` via `Finset.sum_tsub_distrib`). Neither is in mathlib.

Attempt 2 — via the Gauss-norm parent: `gaussNorm_pow_le` (induction from `gaussNorm_mul_le`) then specialise.
  - Mathlib decls used: `MvPowerSeries.gaussNorm_mul_le` (+ a missing `gaussNorm_pow_le`).
  - Result: **fails as a composition.** (i) `gaussNorm_pow_le` does not exist yet (Phase 5). (ii) Converting the project's rpow-free hypothesis `‖[Xʲ]G‖^{p−1} ≤ p^{j−1}` into a `HasGaussNorm`/`gaussNorm G ≤ const` statement at the critical radius `c = p^{−1/(p−1)}` requires `Real.rpow`, real boundedness (`BddAbove`) arguments, and the order-shift, then converting back — far more than 3 calls and involving real analysis the project deliberately sidesteps.

Conclusion: **NOT-COMPOSABLE.** The theorem is a genuine proof resting on two non-trivial project lemmas (`norm_coeff_prod_le`, `pow_norm_sum_le`), not a 1–3-line gluing of mathlib primitives. (Per the Phase 6 heuristics, "multiple `have`s with real reasoning between" = a proof, not a composition.)

---

## Verdict: `PadicLFunctions.norm_coeff_pow_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): concept is standard (Gauss-norm power-submultiplicativity + Legendre); **no source names this exact rpow-free coefficient inequality** — it is an internal step in p-adic-exp well-definedness (Cassels §12, Washington §5.1).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (base ring `ℚ_[p]`; rpow-free encoding vs. real Gauss norm). Phase 4c finds a real modern-idiom target, `gaussNorm_pow_le`, which is a genuine mathlib API gap.
- Mathlib search (Phase 5): **not in mathlib** — neither this form nor `gaussNorm_pow_le`; mathlib has only the binary `gaussNorm_mul_le` and the `IsRestricted` (`≤1`) closure.
- Composition check (Phase 6): **NOT-COMPOSABLE** — rests on project lemmas `norm_coeff_prod_le` + `pow_norm_sum_le`, not ≤3 mathlib calls.

**Rationale (why BORDERLINE, not a self-resolving bucket):**

All four phases completed cleanly and individually point at "novel for mathlib in *some* form" — it is genuinely not in mathlib and not a cheap composition. But synthesising them lands on a judgment the skill cannot make alone, for three concrete reasons. (1) **Form mismatch with the mathlib idiom.** The mathlib-idiomatic contribution here is the *general* `PowerSeries.gaussNorm_pow_le` (an easy induction off the existing `gaussNorm_mul_le`), and this project theorem is a deliberately **rpow-free, `ℚ_[p]`-specific, order-shifted corollary** of it. Mathlib would almost certainly want the general `gaussNorm_pow_le`; whether it *also* wants this exact rpow-free p-adic coefficient corollary (which trades the clean Gauss-norm statement for the integer-power encoding the project needs internally) is a taste call — the rpow-free encoding is a project convenience, not obviously a library asset. (2) **Single internal consumer.** K = 1, used once inside the same file (`summable_prod_family`); there are no external consumers and the only "siblings" (`norm_coeff_pow_le_one`, `…_one'`) are a *different* `≤1` bound re-proved independently — so this specific decaying-bound form has weak demonstrated reuse, which per the Phase-6 signal table leans away from upstreaming the corollary as-is. (3) **The real contribution is upstream of it.** The honest mathlib move is "add `gaussNorm_pow_le`, then derive everyone's coefficient bounds from it" — which would also subsume the project's three near-duplicate `…pow_le_one` lemmas. Whether to do that refactor (and in what form to land the p-adic corollary) is exactly the kind of scope/taste decision the skill must defer.

This is **not** a cost-based downgrade (cost is MODERATE and would not by itself block a YES). It is a genuine *form + scope* ambiguity between `YES-but-generalise-first` (target = `gaussNorm_pow_le`) and `NO-composable`/keep-project-local.

**Numbered questions (for the user):**

1. Do you want to upstream the **general** lemma `PowerSeries.gaussNorm_pow_le : gaussNorm v c (f ^ n) ≤ (gaussNorm v c f) ^ n` (an induction off mathlib's existing `MvPowerSeries.gaussNorm_mul_le`)? If yes, this becomes `YES-but-generalise-first` with that as the target.

2. Is the **rpow-free** `‖·‖^{p−1} ≤ p^{integer}` encoding something you consider mathlib-worthy in its own right, or purely an internal convenience for this project? (If purely internal, the p-adic corollary stays project-local even if `gaussNorm_pow_le` goes up.)

3. Should the three project lemmas with the *related* `≤1` bound — `ResidueZeta.norm_coeff_pow_le_one`, `IwasawaProof.GaloisAction.norm_coeff_pow_le_one'`, and this `norm_coeff_pow_le` — be **consolidated** onto one shared engine (mathlib `gaussNorm_pow_le`, or a `Common/` lemma) first? They are currently three independent re-derivations of closely related coefficient-of-power bounds.

4. Given there is exactly **one** internal call site and no external consumers, are you content to keep `norm_coeff_pow_le` project-local (no mathlib PR for the corollary), contributing only the general `gaussNorm_pow_le` to mathlib?

**Refactor-actionable next steps regardless of the answers:**
- If (1)=yes: run `/generalise PadicLFunctions.norm_coeff_pow_le` aimed at `PowerSeries.gaussNorm_pow_le`; prove it by `induction n` using `MvPowerSeries.gaussNorm_mul_le` (+ `pow_succ`), proposed location `Mathlib/RingTheory/PowerSeries/GaussNorm.lean`, PR title `feat(RingTheory/PowerSeries): add gaussNorm_pow_le`.
- If (3)=yes: open a project dedup ticket to factor the three `…pow_le[_one]` lemmas onto one helper (then this `/mathlibable` re-runs cleanly on the single survivor).
- If (2)/(4) say "keep local": no mathlib action for the corollary; leave it in `PadicExp.lean` as the rpow-free engine for `summable_prod_family`.

---

## Next step

User answers questions 1–4; then re-run `/mathlibable PadicLFunctions.norm_coeff_pow_le` (or, if `gaussNorm_pow_le` is the agreed target, hand off to `/generalise PadicLFunctions.norm_coeff_pow_le`). The likely resolution: contribute the general `PowerSeries.gaussNorm_pow_le` to mathlib (YES-but-generalise-first on the *general* form) while keeping this rpow-free p-adic corollary project-local.
