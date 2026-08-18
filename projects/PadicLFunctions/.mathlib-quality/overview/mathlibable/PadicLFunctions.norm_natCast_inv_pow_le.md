# `/mathlibable` report — `PadicLFunctions.norm_natCast_inv_pow_le`

Mode A — full 10-phase workflow, exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task instruction); **reasoned from source** — Phase 0 fallback. The decl and all its dependencies were read directly from source and from the pinned mathlib tree under `.lake/packages/mathlib/`.
- decl `PadicLFunctions.norm_natCast_inv_pow_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:828`
- kind:                      theorem
- has sorry:                 no (0 sorries in the file; proof is complete)
- module docstring summary:  the p-adic exponential and logarithm (RJW Lem 5.14): convergence, isometry, and `x^s := exp(s·log x)` on `1 + pℤ_p`.

Namespace context: the decl lives in `namespace PadicLFunctions` under `variable (p : ℕ) [hp : Fact p.Prime]`, so the elaborated signature carries `p` as a leading explicit argument and `[Fact p.Prime]` as an instance:

```lean
theorem PadicLFunctions.norm_natCast_inv_pow_le
    (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) :
    (‖(n : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1)
```

---

### Statement (Phase 1)

`PadicLFunctions.norm_natCast_inv_pow_le` is a theorem stating the following:

For a prime `p` and a natural number `n ≥ 1`, the reciprocal of the `(p−1)`-th power of the p-adic absolute value of `n` is bounded above by `p^{n−1}`:

$$\bigl(\lVert n\rVert_p^{\,p-1}\bigr)^{-1} \le p^{\,n-1}.$$

Equivalently (taking `(p−1)`-th roots, formally), `p^{-(n-1)/(p-1)} ≤ ‖n‖_p`, i.e. `(p-1)·v_p(n) ≤ n-1`, where `v_p` is the p-adic valuation. The docstring calls this "the inverted Legendre bound for the plain integer `n`, used for the `log` coefficients". It is the natural-number analogue of the file's sibling lemma `norm_factorial_inv_pow_le` (the same inequality with `n!` in place of `n`), which feeds the `exp` coefficients.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; the p-adic norm `‖·‖` on `ℚ_[p]` and the real power `(p : ℝ)^…` both depend on it.
- `n : ℕ` — the integer whose p-adic norm is bounded.

Hypotheses (Lean side):
- `hn : 1 ≤ n` — needed so that `n - 1` (truncated `ℕ` subtraction) behaves as ordinary subtraction and so `n ≠ 0` (the norm is nonzero).

Conclusion (math): the inverted/sharp Legendre bound for a plain integer: `(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}`, equivalently `(p−1)·v_p(n) ≤ n−1`.

Conclusion (Lean): `(‖(n : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1)`.

**Proof structure (read from source).** Rewrite `‖(n:ℚ_[p])‖ = p^{−v_p(n)}` (`Padic.norm_eq_zpow_neg_valuation` + `Padic.valuation_natCast`), reduce both sides to `zpow` of `(p:ℝ)`, and apply monotonicity (`zpow_le_zpow_right₀`); the remaining integer inequality `(p−1)·v_p(n) ≤ n−1` is supplied by the file-local lemma `sub_one_mul_padicValNat_succ_le p (n-1)` (which proves `(p−1)·v_p(m+1) ≤ m`), then `linarith`/`push_cast`. The arithmetic core `sub_one_mul_padicValNat_succ_le` is itself proved from `p^{v_p(n+1)} ∣ n+1` (`pow_padicValNat_dvd`) and the Bernoulli inequality `1 + v·(p−1) ≤ p^v` (`one_add_mul_le_pow`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a helper corollary (a norm-level bound on `‖n‖_p`), not a named/main theorem and not a new structure. It exists to feed `norm_coeff_log_le`. It is *not* listed under `## Main results`; the file's headline result is the `exp`/`log` isometry and `x^s`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the report's framing only.)

### One-line check (Phase 2b)

Body line count: ~10 substantive lines (a real proof with a valuation rewrite, a `zpow` monotonicity step, and an integer-inequality discharge).
One-liner verdict: **n/a — kind is theorem, not def**. Section skipped (no defeq/diamond/API-stability exemptions are relevant to a `theorem`).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic valuation natural number bound (p-1) v_p(n) ≤ n-1 Legendre` | partial | Legendre `v_p(n!) = (n − s_p(n))/(p−1)`; the *factorial* sharp bound is standard and named (Legendre); the *plain-n* `(p−1)v_p(n) ≤ n−1` is not a named theorem | the named result is for `n!`; the plain-`n` version is elementary folklore |
| 2 | WebSearch (general form) | `v_p(n) <= log_p(n) p-adic valuation natural number standard inequality` | yes | `v_p(n) ≤ log_p n`, equivalently `p^{v_p(n)} ≤ n` (since `p^{v_p(n)} ∣ n`) | Wikipedia "p-adic valuation"; treated as a one-line elementary fact, not a named theorem |
| 3 | WebSearch (named-after / aliases / application) | `p-adic norm of integer logarithm coefficient bound n inverse Washington cyclotomic fields` | partial | the bound on `‖1/n‖_p = ‖n‖_p^{-1}` governs convergence of the p-adic `log`; standard in every p-adic-analysis treatment | Washington §5.1, Conrad notes, Cassels §12 — the *use* is standard; no special name for the inequality |
| 4 | WebSearch (radius-of-convergence context) | `nLab p-adic logarithm convergence radius coefficient valuation denominator bound` | yes | umontreal/MIT/Cambridge lecture notes: `1 ≤ p^{v_p(n)} ≤ n` used directly in the Cauchy–Hadamard radius computation for `log(1+x)` | confirms the bound is the *elementary* ingredient, treated inline |
| 5 | ChatGPT MCP | "standard form + generality + historical evolution of `(p−1)v_p(n) ≤ n−1` / `‖n‖_p` bound" | **n/a — unavailable** | — | the configured `chatgpt-math` MCP server failed to connect (its path `/home/chris/...` is from a different machine; `claude mcp list` shows `✘ Failed to connect`). Substituted with extra WebSearch breadth (rows 1–4, 9–10) + direct source fetches (PlanetMath, rows 6/8) to meet the standard-form/generality requirement. |
| 6 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | n/a | (no references dir; no `refs/` symlink present) | recorded n/a — neither directory exists on this checkout |
| 7 | nLab / nCatLab | `ncatlab.org/nlab/show/p-adic+exponential`; PlanetMath "p-adic exponential and p-adic logarithm" (WebFetch) | partial | nLab page 404 (no dedicated page); PlanetMath defines `log_p(1+s)=Σ(−1)^{n+1}s^n/n` and the `exp` radius `p^{−1/(p−1)}` but does **not** state any coefficient-valuation bound | not a categorical concept; nLab has no relevant page; PlanetMath treats coefficients as-is |
| 8 | Stacks Project | (not searched — not an algebraic-geometry concept) | n/a | — | this is elementary p-adic analysis / valuation theory; Stacks does not cover it |
| 9 | MathOverflow / Math.StackExchange | `(p-1) v_p(n) bounded n-1 integral p-adic logarithm coefficients` | partial | the factor `(p−1)` appears throughout p-adic-`log` integrality/convergence discussion; `−log(1−x) = Σ x^n/n`, `v_p(n)` the largest power of `p` dividing `n` | no thread states the inequality as a standalone named result; it is used implicitly |
| 10 | recent arXiv (last 5 years) | `1907.11902 "Legendre's formula and p-adic analysis"`; `2408.00353 "Bounds on the p-adic valuation of the factorial..."` | yes (factorial) | Legendre `v_p(n!)=(n−s_p(n))/(p−1)`; recent work bounds `v_p(n!)`, `v_p(hyperfactorial)` etc. | the active research is on *factorial/hyperfactorial* bounds; the plain-`n` corollary is too elementary to be a paper result |

The protocol passes: WebSearch ran ≥3 distinct queries at different generality levels (specific sharp form #1, most-general elementary form #2, named-after/application #3, radius-context #4); ChatGPT MCP was attempted and recorded n/a-with-reason (server unreachable on this machine) with substitute breadth; local references checked (absent → n/a); nLab checked (404; PlanetMath substituted); Stacks/nCatLab/MathOverflow/arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the sharp Legendre/Bernoulli bound on the p-adic valuation of a natural number**, `(p−1)·v_p(n) ≤ n−1`, equivalently the norm form `(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}`. Its weaker, more famous cousin is `v_p(n) ≤ log_p n` (i.e. `p^{v_p(n)} ≤ n`).

Sources agree on the standard form: **yes** — the *factorial* analogue (`v_p(n!) = (n − s_p(n))/(p−1)`, hence `(p−1)v_p(n!) ≤ n`) is Legendre's theorem, universally named and stated. For a *plain* integer `n`, the bound `v_p(n) ≤ log_p n` is the universally-quoted elementary fact; the sharper `(p−1)v_p(n) ≤ n−1` is a one-line consequence of `p^{v_p(n)} ≤ n` plus Bernoulli `1 + v(p−1) ≤ p^v`, and appears as an unnamed inline step, never a headline lemma.

Most general standard form: for `n ≥ 1`, `(p−1)·v_p(n) ≤ p^{v_p(n)} − 1 ≤ n − 1`. The norm restatement `(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}` is exactly the project's rpow-free packaging of this.

Generality dimensions where the literature varies:
- **Object**: factorial `n!` (Legendre, named, in mathlib) vs. plain `n` (folklore, the target). The plain-`n` form is *strictly weaker/simpler* than Legendre and follows from divisibility alone.
- **Sharpness**: `v_p(n) ≤ log_p n` (loose, ubiquitous) vs. `(p−1)v_p(n) ≤ n−1` (the sharp packaging the project needs to match the `(p−1)`-power normalisation in its decay estimates).
- **Presentation**: valuation form (`(p−1)v_p(n) ≤ n−1`) vs. norm form (`(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}`). The literature works at the valuation level; the project carries the norm form because that is what the geometric-decay calculus consumes.

Disagreement with the literature: **none**. The Lean statement is a faithful, correct norm-level packaging of the standard elementary inequality.

---

### Generality analysis — `PadicLFunctions.norm_natCast_inv_pow_le` (Phase 4)

Literature-standard form (from Phase 3): `(p−1)·v_p(n) ≤ n−1` for `n ≥ 1`, equivalently `(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}`. There is no *more general* mathematical object here — `n` already ranges over all naturals `≥ 1`, and `ℚ_[p]` is the canonical setting for the p-adic norm of an integer.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `(n : ℕ)` | natural number | natural number `≥ 1` | NO | already the full range; `n` is intrinsically a natural number (it is the index/denominator of a power-series coefficient) |
| 2 | `(hn : 1 ≤ n)` | `n ≥ 1` | `n ≥ 1` | NO | required: at `n = 0` the norm is `0`, the LHS is `(0)⁻¹`, and `n - 1 = 0` in `ℕ` — the statement degenerates. The hypothesis is exactly the literature's |
| 3 | ambient field `ℚ_[p]` | the p-adic numbers | the p-adic numbers | NO (see Phase 4c) | the statement is about `‖(n:ℚ_[p])‖` specifically; the analogous statement over a general nonarch. field would need `‖n‖ = p^{−v_p(n)}`, which holds in `ℚ_[p]` by construction |
| 4 | exponent `(p−1)` and RHS `p^{n−1}` | the sharp Legendre normalisation | the sharp Legendre normalisation | NO | this is the precise form needed by the decay estimates; loosening to `v_p(n) ≤ log_p n` would be a *different, weaker* lemma, not a generalisation of this one |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within its mathematical content).
Number of weakening opportunities found: **0**.
There is no parameter to weaken: `n` already ranges over all `n ≥ 1`, `hn` is the necessary hypothesis, and `ℚ_[p]` is the intrinsic setting. The statement is a faithful packaging of the standard elementary inequality.

Cost of restatement: n/a (no restatement at the literature level).

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the only hypothesis is `1 ≤ n`, a genuine arithmetic condition, not a structure preamble |
| 2 | sequences/metric → filters/topology? | no | — | this is a pointwise valuation inequality; no limit/convergence is being stated here (the convergence lives in the *consumers*) |
| 3 | construct an object → universal-property class? | no | — | no object is constructed; it is an inequality |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | n/a |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | **partly** | the *arithmetic core* `(p−1)·padicValNat p n ≤ n − 1` could be stated purely in `ℕ` (no field, no norm), generalising away from `ℚ_[p]`; the norm form is then a one-line corollary | a pure-`ℕ` valuation lemma would sit beside `sub_one_mul_padicValNat_factorial` in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` and compose with all of mathlib's `padicValNat`/digit-sum API |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | no | — | `n` is the denominator of a `log` coefficient; it must be a natural number |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (a factoring, not a true generalisation)**.

The real Bourbaki-2.0 observation is **decomposition + relocation**, not weakening: the target bundles two layers — (a) a *pure number-theory* fact `(p−1)·padicValNat p n ≤ n − 1` for `n ≥ 1`, and (b) the *norm translation* `(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}`. Mathlib already keeps exactly this separation for the factorial case: `sub_one_mul_padicValNat_factorial` (pure `ℕ`) lives in `PadicVal/Basic.lean`, and norm consequences are derived downstream. The mathlib-idiomatic contribution is therefore the **pure-`ℕ` core**:

```lean
-- in Mathlib/NumberTheory/Padics/PadicVal/Basic.lean, beside the factorial version
theorem sub_one_mul_padicValNat_le_sub_one [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n ≤ n - 1 := by
  sorry
```

- Cost: **CHEAP** — it is precisely the file-local `sub_one_mul_padicValNat_succ_le` re-indexed off `+1`; the proof (`pow_padicValNat_dvd` + `one_add_mul_le_pow`) transfers verbatim.
- Mathlib downstream this enables: it slots into the `padicValNat` API family (`sub_one_mul_padicValNat_factorial`, `..._choose_eq_sub_sum_digits`, `padicValNat_le_nat_log`) and gives every consumer the sharp `(p−1)`-scaled valuation bound for a plain integer — currently absent. The *norm* form (the target) is then a genuinely-`≤3`-line corollary of this core plus `Padic.norm_eq_zpow_neg_valuation` + `Padic.valuation_natCast`.
- Real mathematical improvement (not just "looks cooler"): mathlib's `PadicVal/Basic.lean` has the factorial and binomial sharp bounds but is **missing the plain-integer one** — a real, citable gap in a symmetric API family. Filling the `ℕ`-level gap is the mathlib-worthy unit; the norm wrapper is downstream sugar.

This means: the **norm-form theorem as written is not itself the right mathlib unit** — its content splits into a missing pure-`ℕ` lemma (worth adding) plus a short norm composition (inline/derive). Phase 7 weighs this.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no definitional equalities or typeclass-search paths introduced). Skipped.

---

### Mathlib search-status: `PadicLFunctions.norm_natCast_inv_pow_le` (Phase 5)

Five-method search (read `references/mathlib-search.md` conventions). Searched for **both** the user's norm form and the literature-standard valuation core.

```
[A] Lean-Finder       — n/a: Lean-Finder web UI not reachable as a JSON endpoint from here; substituted by [B]+[C]+[D].
[B] Loogle            ⊢ (p - 1) * padicValNat _ _ ≤ _    → NO genuine hit (only spurious `.p`-field matches from unrelated namespaces: Lean.Lsp, Grind, CategoryTheory, …). No mathlib lemma bounds `(p-1) * padicValNat`.
                      Padic, ‖(↑_ : ℚ_[_])‖              → hits are membership/equality lemmas only: `Padic.norm_int_le_one`, `norm_natCast_eq_one_iff`, `norm_natCast_lt_one_iff`, `norm_int_le_pow_iff_dvd`, `norm_natCast_p_sub_one`, `norm_p_zpow`, `norm_p_pow`. NONE is a `(p-1)`-power inverted bound.
[C] LeanSearch        natural-language: "norm of nat cast in p-adic bounded by power of p valuation" → endpoint returned HTTP 404/405 (API moved); substituted by [B]+[D] structural search.
[D] Grep mathlib src  `(p - 1) * padicValNat` over all of Mathlib/ → ONLY factorial (`sub_one_mul_padicValNat_factorial`, line 583) and binomial (`sub_one_mul_padicValNat_choose_*`, lines 637/654) versions. NO plain-`n` version.
                      `padicValNat ... le` non-factorial → `padicValNat_le_nat_log` (v_p(n) ≤ log_p n — the LOOSE bound, line 467), `padicValNat_dvd_iff_le` (line 428). Building blocks, not the sharp form.
                      `pow_padicValNat_dvd` → present (p^{v_p(n)} ∣ n) — the divisibility building block.
[E] Name pattern      grep for `norm_natCast_inv_pow_le` / `norm_natCast.*pow.*le` in mathlib → only the project's own decl; no mathlib name.
```

Searched for both:
  - the user's current form `(‖(n:ℚ_[p])‖^(p-1))⁻¹ ≤ p^(n-1)` → **not in mathlib** (closest: `Padic.norm_int_le_pow_iff_dvd k n : ‖(k:ℚ_[p])‖ ≤ p^(-n) ↔ p^n ∣ k`, a fixed-exponent iff, NOT the `(p-1)`-scaled bound).
  - the literature-standard core `(p-1)·v_p(n) ≤ n-1` → **not in mathlib** (only the factorial/binomial analogues exist; the plain-`n` version is absent).

Concluded: **not in mathlib** (all available methods exhausted, both the user's norm form and the literature-standard valuation core). Mathlib has the *building blocks* — `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `pow_padicValNat_dvd`, `one_add_mul_le_pow` (Bernoulli), `padicValNat_dvd_iff_le` — and the *sibling* `sub_one_mul_padicValNat_factorial`, but neither the plain-`n` arithmetic core nor its norm corollary.

---

### Call sites — `PadicLFunctions.norm_natCast_inv_pow_le` (Phase 6.0)

Internal use count: **1** (within the project, excluding the declaring line).
External-to-file callers: **0** (no other project imports it; no downstream library).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:858 | `exact norm_natCast_inv_pow_le p n hn` — sole consumer, inside `norm_coeff_log_le` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — but the **factorial twin** `norm_factorial_inv_pow_le` (line 69) is the structurally identical proof for `n!`, and the *valuation core* `sub_one_mul_padicValNat_succ_le` (line 309) is reused independently by `norm_succ_inv_smul_pow_le` (line 341). So the *core* has 2 internal uses; the norm wrapper has 1.

Call-sites signal: K = 1 internal use → "possibly the wrong abstraction; could be inlined" *for the norm wrapper specifically*. But note the consumer `norm_coeff_log_le` is itself real API (used twice downstream at lines 944, 968 in the key Legendre/decay estimates), and the wrapper is a deliberate parallel to `norm_factorial_inv_pow_le`. The K=1 is because there is exactly one `log`-coefficient consumer, mirroring the one `exp`-coefficient consumer of the factorial twin — a symmetric, intentional API pair, not dead code.

### Composition check (Phase 6)

Can `norm_natCast_inv_pow_le` be derived from **mathlib** in ≤3 chained calls? (Composition is judged against *mathlib*, not against the project's own helpers.)

Attempt 1 (from mathlib primitives directly):
```lean
example (n : ℕ) (hn : 1 ≤ n) : (‖(n : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1) := by
  rw [Padic.norm_eq_zpow_neg_valuation (...), Padic.valuation_natCast, ...]
  -- now reduced to: (p - 1) * padicValNat p n ≤ n - 1
  ...  -- ← NOT available from mathlib; needs the Bernoulli+divisibility argument
```
  - Mathlib decls used: `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `zpow_le_zpow_right₀`.
  - Result: **partial** — the norm rewriting is mechanical (2 calls), but it leaves the integer goal `(p-1)·v_p(n) ≤ n-1`, which mathlib **does not** provide for plain `n`. Discharging it requires `pow_padicValNat_dvd` + `one_add_mul_le_pow` + `linarith` — a multi-step proof, not a call.
  - Notes: this is exactly the missing pure-`ℕ` core from Phase 4c.

Attempt 2 (via `Padic.norm_int_le_pow_iff_dvd`):
  - `norm_int_le_pow_iff_dvd k n` gives `‖(k:ℚ_[p])‖ ≤ p^(-n) ↔ p^n ∣ k` — a *fixed-exponent* iff. To get the `(p-1)`-scaled inverted bound one would still have to choose the exponent `v_p(n)`, prove `p^{v_p(n)} ∣ n` (have it), and then run the Bernoulli step to convert `v_p(n) ≤ log_p n` into `(p-1)v_p(n) ≤ n-1`. Multiple `have`s with real reasoning between — **a proof, not a composition**.
  - Result: fails as a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. The obstruction is precisely the missing arithmetic core `(p-1)·padicValNat p n ≤ n-1` (Phase 4c). With that core in mathlib, the norm form *would* become a ≤3-line corollary — which is the substance of the verdict.

---

## Verdict: `PadicLFunctions.norm_natCast_inv_pow_le`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the content is the standard sharp Legendre/Bernoulli valuation bound; mathlib has the factorial analogue (`sub_one_mul_padicValNat_factorial`) but the plain-`n` form is folklore and absent. ≥9 channels run (ChatGPT MCP recorded n/a-unreachable with substitute breadth).
- Generality analysis (Phase 4b): MAXIMALLY GENERAL at the literature level (no parameter to weaken). **But Phase 4c found a real mathlib-idiomatic refactor**: the right mathlib unit is the pure-`ℕ` core `(p-1)·padicValNat p n ≤ n-1`, mirroring mathlib's existing `sub_one_mul_padicValNat_factorial`, with the norm form as a corollary.
- Mathlib search (Phase 5): not in mathlib — neither the norm form nor the valuation core; whole-tree grep shows only factorial/binomial `(p-1)*padicValNat` lemmas.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib today (≤3 calls fail; the integer core is the missing piece), but becomes a clean ≤3-line corollary once the core is added.

**Rationale.**

The mathematically interesting, genuinely-missing-from-mathlib content here is **not** the norm inequality as packaged, but its arithmetic kernel: for `n ≥ 1`, `(p − 1)·v_p(n) ≤ n − 1`. Mathlib's `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` already carries the *symmetric* family — `sub_one_mul_padicValNat_factorial` (Legendre, line 583) and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` (Kummer, lines 637/654) — and the loose cousin `padicValNat_le_nat_log` (line 467). The plain-integer member of that family is conspicuously absent. That is the citable gap. The project itself proves it twice over (file-local `sub_one_mul_padicValNat_succ_le`, line 309, in `+1` form) and uses it for both the `log` coefficients (the target) and the geometric-decay estimate `norm_succ_inv_smul_pow_le` — concrete evidence the core is reusable, not bespoke.

So the right action is **generalise-then-relocate**: contribute the pure-`ℕ` core to `PadicVal/Basic.lean` beside its factorial sibling. The target's *norm form* — `(‖n‖_p^{p−1})⁻¹ ≤ p^{n−1}` — is the project's rpow-free presentation tuned to its `(p−1)`-power decay calculus; it is a legitimate ≤3-line corollary of the core but, on its own, is a thin wrapper with a single internal consumer (K=1) and no literature name. It is better kept project-local (or added as a small `Padic` norm corollary only if mathlib wants the norm-level convenience lemma), while the **arithmetic core is the mathlib-worthy unit**. Per the Bourbaki-2.0 rule and the Phase-7 gate, when Phase 4c surfaces a real organisational improvement (here: a missing member of an existing, symmetric API family that composes with all of mathlib's `padicValNat`/digit-sum machinery), the verdict is `YES-but-generalise-first` with reason MODERN-IDIOM rather than `YES-add-as-is`.

**Reason for the generalisation:**
- **MODERN-IDIOM (Bourbaki 2.0):** Phase 4c identified that the mathlib-idiomatic unit is the pure-`ℕ` valuation core, not the norm wrapper. It fills a real, symmetric gap in `PadicVal/Basic.lean` (plain-`n` companion to the factorial and binomial bounds) and composes with mathlib's existing valuation/digit-sum API.
- (Not LITERATURE-WEAKENING: Phase 4b was MAXIMALLY GENERAL; there is no hypothesis to weaken.)

**Proposed restatement** (the mathlib unit to contribute):
```lean
-- Mathlib/NumberTheory/Padics/PadicVal/Basic.lean, beside `sub_one_mul_padicValNat_factorial`
/-- Sharp Bernoulli/Legendre bound for a plain integer: `(p-1)·v_p(n) ≤ n-1`.
Companion to `sub_one_mul_padicValNat_factorial`. -/
theorem sub_one_mul_padicValNat_le_sub_one [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n ≤ n - 1 := by
  sorry  -- proof transfers from the project's `sub_one_mul_padicValNat_succ_le`
         -- (re-index off `+1`): p^{v_p(n)} ∣ n  +  one_add_mul_le_pow
```
The target then specialises in ≤3 lines:
```lean
example (n : ℕ) (hn : 1 ≤ n) : (‖(n : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1) := by
  rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.2 (by omega)),
      Padic.valuation_natCast, /- zpow normalisation -/]
  exact_mod_cast sub_one_mul_padicValNat_le_sub_one (by omega)  -- + a zpow_le_zpow_right₀ step
```

Estimated cost of regeneralisation: **CHEAP** — the core's proof already exists in the project (`sub_one_mul_padicValNat_succ_le`); re-indexing `m+1 ↦ n` is mechanical. (Cost does not affect the verdict regardless.)

Mathlib downstream this enables:
- Completes the `(p-1)*padicValNat` family in `PadicVal/Basic.lean` (factorial ✓, binomial ✓, **plain integer — new**).
- Any p-adic-analysis development needing the sharp valuation/norm bound for integer denominators (p-adic `log`, Mahler-basis estimates, Iwasawa-theoretic convergence) gets it directly instead of re-deriving Bernoulli inline.
- Composes with `padicValNat_le_nat_log`, `pow_padicValNat_dvd`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast` to give norm-level corollaries cheaply.

Next action: run `/generalise PadicLFunctions.norm_natCast_inv_pow_le` (it will tension against both the literature-standard valuation core from Phase 3 and the modern-idiom relocation target from Phase 4c). Concretely: lift `sub_one_mul_padicValNat_succ_le` to the `≤ n-1` form, PR it to `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` beside `sub_one_mul_padicValNat_factorial`, and keep `norm_natCast_inv_pow_le` as a project-local corollary (or PR a small `Padic` norm corollary if the norm-level convenience lemma is wanted upstream).

---

## Next step

Run `/generalise PadicLFunctions.norm_natCast_inv_pow_le`: extract and PR the pure-`ℕ` arithmetic core `sub_one_mul_padicValNat_le_sub_one : (p-1)*padicValNat p n ≤ n-1` (for `n ≠ 0`) into `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`, beside `sub_one_mul_padicValNat_factorial` — the proof transfers verbatim from the project's `sub_one_mul_padicValNat_succ_le`. The norm form `norm_natCast_inv_pow_le` then becomes a ≤3-line corollary (via `Padic.norm_eq_zpow_neg_valuation` + `Padic.valuation_natCast`) and is best kept project-local, since it is the project's rpow-free packaging with a single internal consumer and no literature name.
