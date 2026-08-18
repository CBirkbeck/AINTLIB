# `/mathlibable` report — `PadicLFunctions.norm_factorial_inv_pow_le`

**Final verdict: `BORDERLINE-needs-human`** (grain/packaging call — see Phase 7).

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task instructions); **reasoned from source** — Phase 0 fallback. All building blocks verified to exist in the pinned mathlib at `.lake/packages/mathlib/`.
- decl `PadicLFunctions.norm_factorial_inv_pow_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:69`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` converges and is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}`; `log(1+y)` inverts it; realises RJW Lemma 5.14 (Cassels §12 / Washington §5.1).

---

### Statement (Phase 1)

`norm_factorial_inv_pow_le` is a theorem stating the following:

> For a prime `p` and an integer `n ≥ 1`, the `p`-adic norm of `n!` satisfies the **inverted Legendre bound**
> `(‖n!‖_p)^{−(p−1)} ≤ p^{n−1}`,
> equivalently `‖n!‖_p ≥ p^{−(n−1)/(p−1)}`.

This is the rpow-free, raised-to-the-`(p−1)`-power form of the classical lower bound on `|n!|_p` that controls the convergence radius `p^{−1/(p−1)}` of the `p`-adic exponential. It is proved by inverting both sides of its immediate predecessor `norm_factorial_le` (which gives `p^{−(n−1)} ≤ ‖n!‖_p^{p−1}`), which in turn rests on the mathlib Legendre inequality `sub_one_mul_padicValNat_factorial_lt_of_ne_zero : (p−1)·v_p(n!) < n`.

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[Fact p.Prime]` — the prime.
- `{n : ℕ}` — the index; the factorial argument.
- (no normed-field/algebra variables are used by this lemma — it is purely about `ℚ_[p]`.)

Hypotheses (Lean side):
- `(hn : 1 ≤ n)` — `n ≥ 1`, so `n − 1` (ℕ subtraction) and the exponent `p^{n−1}` behave.

Conclusion (math): `‖n!‖_p^{−(p−1)} ≤ p^{n−1}` (a lower bound on the `p`-adic size of `n!`, in inverted-power packaging).

Conclusion (Lean): `(‖(n.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper corollary in the `## ` decomposition cluster R5.E for the p-adic exp; it is the one-step inversion of the sibling lemma `norm_factorial_le`. Not a main result, not a named theorem, introduces no structure.

(Note: literature width was EXHAUSTIVE regardless — all nine channels run below.)

### One-line check (Phase 2b)

Body line count: ~5 substantive lines (one `rw` of an equational `show`, then a single `exact inv_anti₀ … (norm_factorial_le …)`).
One-liner verdict: **n/a — kind is `theorem`, not a `def`.** (The defeq/diamond/API exemptions do not apply to propositions.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic valuation of factorial Legendre formula bound v_p(n!) (n − s_p(n))/(p−1)" | yes | `v_p(n!) = (n − s_p(n))/(p−1)`; ≤ form `v_p(n!) ≤ (n−1)/(p−1)` | Eremin *Legendre's formula and p-adic analysis* (arXiv 1907.11902); cut-the-knot; AoPS. Confirms the *equality* and the digit-sum form our `norm_factorial_le` uses. |
| 2 | WebSearch (general / coarser bound) | "Legendre's formula sum of digits p-adic valuation factorial inequality" | yes | `v_p(n!) ≤ n/(p−1)` (coarsest) and `≤ (n−1)/(p−1)` (since `s_p(n) ≥ 1`) | Wikipedia *Legendre's formula*; AoPS. Our lemma uses the sharper `s_p(n) ≥ 1` version. |
| 3 | WebSearch (named-after / aliases, applied form) | "p-adic norm of n factorial bound exponential convergence radius nonarchimedean" | yes | `\|n!\|_p` small; radius `p^{−1/(p−1)}` | **Keith Conrad, *Infinite series in p-adic fields*** (canonical reference): "Legendre's formula implies a bound on val(m!) … as a consequence exp(z) has radius of convergence `p^{−1/(p−1)}`." This is *exactly* our use. |
| 4 | ChatGPT MCP | (MCP server not configured in this environment) — substituted with WebSearch synthesis explicitly asking for standard form + generality + historical form: "p-adic exponential isometry open ball radius p^(−1/(p−1)) norm factorial inverse bound Cassels Washington" | yes | radius `p^{−1/(p−1)}`; `exp : 𝔻 → 1+𝔻` bijection; proof "requires basic estimates of `v_p(n!)`" | n/a for the MCP tool itself; recorded as substituted. Wikipedia *P-adic exponential function*; MIT notes (math.mit.edu/~dav/exp.pdf); Cassels *Local Fields* cited as the classical source — matches the file's RJW/Cassels §12 citation. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/` and `refs/PadicLFunctions/` | n/a | (no references dir; `refs/` absent in this checkout) | Recorded n/a — PDFs are local-only and not present here. The project's own `worklist.json`/decomposition labels the cluster R5.E. |
| 6 | nLab | "p-adic exponential map" (`ncatlab.org/nlab/show/p-adic+exponential+map`) | n/a | HTTP 404 — no dedicated nLab page | nLab has no standalone p-adic-exponential entry; the concept is covered under classical p-adic analysis references, not a categorical nLab page. |
| 7 | nCatLab (categorical) | — | n/a | not a categorical concept | A scalar inequality on `\|n!\|_p`; nothing categorical to look up. |
| 8 | Stacks Project | — | n/a | not an algebraic-geometry concept | Legendre's formula / p-adic factorial norm is analytic number theory, not scheme theory. |
| 9 | MathOverflow / Math.StackExchange | (covered transitively by queries 1–4; the radius-`p^{−1/(p−1)}` and `v_p(n!) ≤ (n−1)/(p−1)` facts are textbook, surfaced via ProofWiki / AoPS / cut-the-knot hits) | yes | same as #2–#3 | No MO-specific subtlety; the bound is standard and uncontested. |
| 10 | recent arXiv (last 5 years) | "bounds p-adic valuation factorial hyperfactorial superfactorial 2408.00353" | yes | upper/lower bounds for `v_p(n!)` via Legendre–de Polignac | Pain, arXiv **2408.00353** (2024) — confirms the `v_p(n!)` bound is still the object of current notes; the precise `(n−1)/(p−1)` upper bound is the standard one. |

**Protocol pass check:** WebSearch ran 4 distinct queries at three generality levels (sharp equality, coarse `≤`, applied-to-exp form); ChatGPT MCP unavailable → explicitly substituted by a 4th WebSearch asking for standard form + generality + classical (Cassels/Washington) source; local refs checked (n/a); nLab checked (404, no page); nCatLab / Stacks recorded n/a with reasons; MathOverflow covered transitively; recent arXiv (2408.00353) checked. All nine channels addressed.

### Literature summary (Phase 3)

Concept identified as: **the lower bound on the `p`-adic norm of `n!`** coming from **Legendre's formula** (a.k.a. Legendre–de Polignac), `v_p(n!) = (n − s_p(n))/(p−1) ≤ (n−1)/(p−1)`, used to establish the convergence radius `p^{−1/(p−1)}` of the `p`-adic exponential.
Sources agree on the standard form: **yes** — the equality `v_p(n!) = (n − s_p(n))/(p−1)` and its corollary `v_p(n!) ≤ (n−1)/(p−1)` are textbook (Conrad, Cassels, Wikipedia, AoPS, Eremin, Pain).
Most general standard form: a statement about `v_p(n!)` over ℕ (Legendre's formula), from which the `‖·‖_p` real-valued bound is an immediate translation via `‖x‖_p = p^{−v_p(x)}`.
Generality dimensions where the literature varies:
  - Sharpness: `n/(p−1)` (coarse) vs `(n − s_p(n))/(p−1)` (exact). Our lemma uses the intermediate `(n−1)/(p−1)` (i.e. `s_p(n) ≥ 1`), which is the right sharpness for the exp radius.
  - Packaging: literature states it as a *valuation* fact over ℕ; our lemma is the *norm* fact over ℝ, raised to `(p−1)` and inverted to stay rpow-free.
Disagreement with the literature: **none.** The mathematics is exactly the standard Legendre bound; the project merely re-packages it into the rpow-free inverted-power norm form it needs.

---

### Generality analysis — `norm_factorial_inv_pow_le`

Literature-standard form (from Phase 3): Legendre's bound `v_p(n!) ≤ (n−1)/(p−1)`, i.e. `‖n!‖_p ≥ p^{−(n−1)/(p−1)}`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]` | a rational prime | a rational prime | NO | Legendre's formula is intrinsically about a prime `p`; cannot weaken. |
| 2 | base field `ℚ_[p]` | the `p`-adic numbers | could be any extension with `‖·‖` extending the `p`-adic norm | borderline | The bound is about `‖(n! : ℚ_[p])‖`; in any normed `ℚ_[p]`-algebra the image norm equals `‖(n!:ℚ_[p])‖` (isometric on ℚ_[p]), so the lemma generalises *trivially* by `norm_algebraMap`. But mathlib's `Padic.norm_eq_zpow_neg_valuation` is stated for `ℚ_[p]`; keeping it on `ℚ_[p]` is standard. |
| 3 | `(hn : 1 ≤ n)` | `n ≥ 1` | `n ≥ 1` (for `n = 0`, `n! = 1`, both sides `= 1`, also true) | yes (could drop to `n : ℕ` with `n−1` ℕ-truncated) | At `n = 0`: LHS `= (‖1‖^{p−1})⁻¹ = 1`, RHS `= p^0 = 1`, so `≤` holds with equality. The `hn` hypothesis is removable but harmless; trivial weakening. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (modulo two trivial/harmless points: removing `hn`, and the isometric base-change to any normed `ℚ_[p]`-algebra — neither changes the mathematical content).
Number of weakening opportunities found: 0 substantive (2 cosmetic).
Proposed restatement: none needed for generality. (If folded into mathlib, the natural form is a `padicValNat`→`‖·‖` bridge lemma, not a weakening — see Phase 4c.)
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | All hypotheses are already typeclass (`Fact p.Prime`); no bundled preamble. |
| 2 | sequences/metric → filters/topology? | no | — | This is a single scalar inequality; no limit/convergence to filter-ise. |
| 3 | construct an object → universal property? | no | — | No object constructed; it is a bound. |
| 4 | set-with-closure → bundled substructure? | no | — | n/a. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | no (cosmetic only) | could state over any normed `ℚ_[p]`-algebra via `norm_algebraMap`, but content is unchanged | marginal; the `ℚ_[p]` form is the canonical one. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/ordered structure? | no | — | The index `n` is the factorial argument; intrinsically ℕ. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: This is a concrete scalar inequality on `‖(n!:ℚ_[p])‖`; there is no preamble to classify, no construction to characterise, and no metric/sequence notion to filter-ise. The only "reformulation" is the natural mathlib *packaging* (a `padicValNat`→norm bridge lemma) discussed in Phase 7 — that is a grain question, not a Bourbaki-2.0 modernisation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `norm_factorial_inv_pow_le`

[A] Lean-Finder       "lower bound p-adic norm of factorial", "‖n!‖ p ≥ p^…"   n/a: Lean-Finder web service not reachable from this sandboxed environment — substituted by [D] grep + [E] name-pattern over the pinned mathlib tree.
[B] Loogle            `(‖(_ : ℚ_[_])‖ ^ _)⁻¹ ≤ _ ^ _`, `‖(Nat.factorial _ : ℚ_[_])‖`   n/a: Loogle web service not reachable — substituted by [D] type-shape grep below.
[C] LeanSearch        "p-adic norm of factorial bound", "valuation of factorial inequality"   n/a: LeanSearch web service not reachable — substituted by [D]/[E].
[D] Grep mathlib src  `‖.*factorial.*‖.*≤`, `factorial.*p ^`, `padicValNat.*factorial`, `norm_factorial`, `padicExp`   **partial hits** — see below.
[E] Name pattern      `norm_factorial`, `factorial.*norm`, `sub_one_mul_padicValNat_factorial*`, `padicValNat_factorial*`   hits on the **valuation** lemmas only.

Searched for both:
  - the user's current form `(‖(n!:ℚ_[p])‖^{p−1})⁻¹ ≤ p^{n−1}` — **no hit** anywhere in mathlib.
  - the literature-standard valuation form — **HIT**: `sub_one_mul_padicValNat_factorial_lt_of_ne_zero [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) : (p − 1) * padicValNat p n.factorial < n` at `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:591` (Legendre's formula corollary; the file also has `sub_one_mul_padicValNat_factorial`, `padicValNat_factorial`, `padicValNat_factorial_le`). This is the **valuation** (ℕ) form; the **norm** (ℝ) form our lemma states is NOT in mathlib.

Building blocks confirmed present in mathlib (all used by the proof chain):
  - `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` — `PadicVal/Basic.lean:591` (the Legendre content).
  - `Padic.norm_eq_zpow_neg_valuation` — `PadicNumbers.lean:304` / `PadicIntegers.lean:341`.
  - `Padic.valuation_natCast` — used in `norm_factorial_le` (exists in `Padics`).
  - `inv_anti₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1226`.
  - `zpow_le_zpow_right₀` — `Basic.lean:994`; `zpow_pos`, `zpow_neg`, `zpow_natCast` — standard.

Adjacent (different) norm-of-factorial facts in mathlib:
  - `Mathlib/NumberTheory/Padics/MahlerBasis.lean:56` — `‖(ascPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℤ_[p])‖`: about Mahler bases; **different statement**, not a `p^{n−1}` bound.
  - `Mathlib/Analysis/Complex/Exponential.lean:376–483` — `‖exp x − ∑ xᵐ/m!‖ ≤ …`: the **Archimedean** complex-exp tail bounds; unrelated to the `p`-adic norm of `n!`.
  - **No `padicExp` / p-adic exponential exists in mathlib at all** (grep for `padicExp`/`expPadic` empty) — the entire supporting API, including this bound, is genuinely absent.

Concluded: **"not in mathlib in this (norm/ℝ) form — all substituted search methods exhausted, plus the literature-standard form."** Mathlib has the *valuation-form* Legendre corollary (`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`) and all the norm↔valuation translation primitives, **but not the packaged norm bound** `(‖n!‖^{p−1})⁻¹ ≤ p^{n−1}`.

---

### Call sites — `norm_factorial_inv_pow_le`

Internal use count: **3** (within `PadicLFunctions`, not counting the declaration itself; all three are in the same declaring file `PadicExp.lean`).
External-to-file callers: 0 distinct *other* files (all uses are downstream lemmas inside `PadicExp.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:85  | `have hfac := norm_factorial_inv_pow_le p hn` — inside `norm_factorial_inv_smul_pow_le` (the geometric decay bound for exp terms) |
| PadicExp.lean:184 | `refine mul_le_mul (norm_factorial_inv_pow_le p (by omega)) …` — inside `norm_factorial_inv_smul_pow_sub_lt` (strict tail domination) |
| PadicExp.lean:850 | `exact norm_factorial_inv_pow_le p hn` — inside `norm_coeff_exp_le` (`‖[Xⁿ]exp‖^{p−1} ≤ p^{n−1}`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_factorial_inv_pow_le`?):
  - The sibling `norm_natCast_inv_pow_le` (PadicExp.lean:848) and `norm_succ_inv_smul_pow_le` (:326) prove the *analogous* bound for the plain integer `n` / the `log` denominators `(n+1)` — they re-run the same `Padic.norm_eq_zpow_neg_valuation` + `zpow_le_zpow_right₀` pattern rather than calling this lemma, because the factorial vs. `n` vs. `(n+1)` cases differ. So the *pattern* recurs 3× across the file, each instance tied to a different denominator. Not a literal re-derivation of *this* lemma.

What the pattern tells us: K = 3 internal uses, no inline re-derivation of this exact lemma → it is **real, used API** within the file. Phase-7 leaning would normally be YES-* — but the composability twist (below) and the grain question pull it to BORDERLINE.

---

### Composition check (Phase 6)

Can `norm_factorial_inv_pow_le` be derived **from mathlib** in ≤3 chained calls?

Attempt 1: `inv_anti₀ (zpow_pos hp_pos _) (norm_factorial_le p hn)` after one rewrite of `p^{n−1}` to `(p^{−(n−1)})⁻¹`.
  - Decls used: `inv_anti₀` (mathlib), `zpow_pos` (mathlib), **`norm_factorial_le` (PROJECT-LOCAL — `PadicExp.lean:52`, NOT mathlib)**.
  - Result: **partial** — it is a clean 2-call composition (literally the lemma's own proof body), but the substantive call `norm_factorial_le` is **not a mathlib primitive**; it is the sibling lemma that does the actual Legendre→norm translation.
  - Notes: This is the crux. The composition is trivial *given* `norm_factorial_le`, but `norm_factorial_le` itself is absent from mathlib.

Attempt 2 (composing from mathlib *primitives only*, inlining `norm_factorial_le`):
  - Sketch: `rw [Padic.norm_eq_zpow_neg_valuation hf0, Padic.valuation_natCast, …]; refine inv_anti₀ …; … sub_one_mul_padicValNat_factorial_lt_of_ne_zero …; linarith`.
  - Decls used: `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `zpow_*`, `inv_anti₀`, `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, `linarith` — i.e. the *combined* bodies of `norm_factorial_le` **and** `norm_factorial_inv_pow_le`.
  - Result: **fails the ≤3-call bar** — this is ~10 lines with `rw` chains, an `exact_mod_cast`, and `linarith` (a real proof, per the Phase-6 heuristics "anything requiring `rw […]; … linarith` is a proof, not a composition").

Conclusion: **NOT-COMPOSABLE from mathlib primitives** (Attempt 2 is a genuine multi-step proof). The only ≤3-call route (Attempt 1) routes through the **project-local** `norm_factorial_le`, so it is not a mathlib composition. The honest mathlib unit of work is therefore the **pair** `norm_factorial_le` + `norm_factorial_inv_pow_le` (or a single norm-of-factorial bridge lemma), not this corollary in isolation.

---

## Verdict: `PadicLFunctions.norm_factorial_inv_pow_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): standard **Legendre bound** `v_p(n!) ≤ (n−1)/(p−1)`; norm form `‖n!‖_p ≥ p^{−(n−1)/(p−1)}`; canonical reference Keith Conrad's *Infinite series in p-adic fields* (also Cassels, Washington §5.1, Eremin 1907.11902, Pain 2408.00353). The mathematics is textbook and uncontested.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (Phase 4b); no modern-idiom reformulation (Phase 4c) — only the cosmetic packaging-as-mathlib-bridge point.
- Mathlib search (Phase 5): the **valuation form** is in mathlib (`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, `PadicVal/Basic.lean:591`); the **norm form** this lemma states is **not** in mathlib, and there is **no p-adic exponential** in mathlib at all.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib primitives** (the only short route goes through the project-local sibling `norm_factorial_le`; inlining mathlib primitives is a ~10-line `rw`/`linarith` proof).

**Rationale (1–2 paragraphs):**

The content is genuinely missing from mathlib in this form: mathlib has Legendre's formula as a *valuation* statement over ℕ but nowhere translates it to the *norm* bound `(‖n!‖^{p−1})⁻¹ ≤ p^{n−1}` on `ℚ_[p]`, and mathlib has no p-adic exponential machinery whatsoever, so this bound (and its three downstream consumers) are not redundant with anything upstream. That rules out `NO-mathlib-has-it`. It is also not a clean `NO-composable-from-mathlib`: the only ≤3-call derivation routes through the **project-local** lemma `norm_factorial_le` (which is itself absent from mathlib), and inlining true mathlib primitives produces a real multi-step proof — so by the skill's "composition from *mathlib*" test it is NOT-COMPOSABLE.

What blocks a clean YES is purely a **grain / packaging** judgment that the skill cannot make alone. This theorem is the **one-step inversion** (`inv_anti₀`) of its sibling `norm_factorial_le`; shipping *this corollary by itself* to mathlib would be wrong, and the file deliberately keeps the two as a forward/inverted pair plus near-identical siblings for `n` (`norm_natCast_inv_pow_le`) and for the log denominators (`norm_succ_inv_smul_pow_le`). The right mathlib unit is almost certainly a **single, more fundamental "norm of `n!` in `ℚ_[p]`" lemma** (a `padicValNat`→`‖·‖` bridge) from which both this and `norm_factorial_le` are immediate — but choosing that target, its statement, and whether to fold in the `n`/`(n+1)` siblings is a mathematical-taste + project-policy call. Per the skill, a verdict that hinges on grain/packaging taste is `BORDERLINE-needs-human`, not a self-resolved YES.

**Numbered questions (≤5):**

1. **Grain:** Do you want to upstream a single canonical lemma about `‖(n! : ℚ_[p])‖` (e.g. `Padic.norm_factorial_le`/`…_ge`, a `padicValNat`→norm bridge) — from which both `norm_factorial_le` and this inverted form follow in one line — rather than this corollary on its own? (yes → the mathlib target is the bridge lemma, and this becomes `NO-composable-from-mathlib` *relative to that new lemma*; no → go to Q2.)
2. **Pair vs. single:** If not the bridge lemma, would you ship `norm_factorial_le` **and** `norm_factorial_inv_pow_le` as one PR (forward + inverted), accepting that the inverted one is a trivial `inv_anti₀` corollary kept for ergonomics? (yes → `YES-add-as-is` for the pair, this report's lemma riding along; no → go to Q3.)
3. **Form:** Mathlib's idiom would likely prefer the rpow form `‖(n!:ℚ_[p])‖ ≥ (p:ℝ)^(−(n−1)/((p:ℝ)−1))` (using `Real.rpow`) over the project's rpow-free `^(p−1)`-raised packaging, since the `(p−1)` power is a project-internal convenience for ultrametric `pow`-monotonicity. Are you willing to restate in the rpow form for mathlib (more recognisable, but the project's downstream proofs rely on the rpow-free shape)? (yes/no — affects the proposed statement.)
4. **Scope:** Is upstreaming any of the p-adic exp/log API (RJW Lem 5.14 cluster R5.E) actually on your roadmap, or is this purely an internal `PadicLFunctions` development for now? (If purely internal, the whole cluster including this lemma should stay project-local and is not a mathlib candidate yet — a `NO`-by-scope.)

**Next action:** user answers Q1–Q4; re-run `/mathlibable PadicLFunctions.norm_factorial_inv_pow_le` (with the chosen mathlib target as a Phase-1 input). Likely resolutions:
  - Q1 = yes → re-aim at the new bridge lemma; this corollary becomes `NO-composable-from-mathlib` (one `inv_anti₀` call from the bridge), inlined at the 3 sites.
  - Q2 = yes → `YES-add-as-is` for the `{norm_factorial_le, norm_factorial_inv_pow_le}` pair as one PR to `Mathlib/NumberTheory/Padics/`.
  - Q4 = internal-only → drop from mathlib consideration; keep as project-local helper.

---

## Next step

User answers the four numbered questions above; then re-run `/mathlibable PadicLFunctions.norm_factorial_inv_pow_le` with the chosen mathlib target (bridge lemma / pair / rpow form) as a Phase-1 input to resolve the bucket. If the p-adic exp/log cluster is not slated for upstreaming, treat the whole cluster (this lemma included) as project-local and out of mathlib scope for now.
