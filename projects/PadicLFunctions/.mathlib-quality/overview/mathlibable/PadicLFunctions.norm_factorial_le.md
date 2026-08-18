# `/mathlibable` report — `PadicLFunctions.norm_factorial_le`

**Final verdict: `NO-composable-from-mathlib`** (the rpow-free norm bound is a
short composition of mathlib's Legendre inequality with the p-adic
norm↔valuation bridge; it is project-internal glue, not a mathlib-shaped
lemma). See Phase 7 for the refactor-actionable detail.

---

### Baseline (Phase 0)

- lake build:               build **not** re-run (per task note: stale/slow); reasoned from source. The declaration and all dependencies read directly.
- decl `PadicLFunctions.norm_factorial_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:52`
- kind:                      theorem
- has sorry:                 no (self-contained proof, lines 52–61)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — defines `exp(x)=∑xⁿ/n!`, proves it converges and is an isometry on the open ball `‖x‖ < p^{−1/(p−1)}`, and `log` inverts it. `norm_factorial_le` is auxiliary lemma **E2**, the Legendre denominator bound that powers the convergence estimates.

---

### Statement (Phase 1)

`norm_factorial_le` is a theorem stating the following:

> For a prime `p` and an integer `n ≥ 1`, the `p`-adic norm of `n!` (as an
> element of `ℚ_[p]`) satisfies, in rpow-free `(p−1)`-th-power form,
> `p^{−(n−1)} ≤ ‖n!‖_p^{\,p−1}`.

This is exactly Legendre's bound `v_p(n!) ≤ (n−1)/(p−1)` re-expressed on the
norm side. Since `‖n!‖_p = p^{−v_p(n!)}`, the inequality
`(p−1)·v_p(n!) ≤ n−1` is equivalent to `p^{−(n−1)} ≤ (p^{−v_p(n!)})^{p−1} = ‖n!‖_p^{\,p−1}`.
The `^(p−1)` packaging is a deliberate device to keep everything in integer
`zpow`/`pow` and avoid `Real.rpow` (the `p^{−1/(p−1)}` radius is never
formed as a real power anywhere in the file — `InExpBall` at line 65 is
likewise stated as `‖x‖^{p−1} < p⁻¹`).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the prime (the whole file's ambient prime).
- *No* `L`-algebra typeclasses are used: the statement is purely about `ℚ_[p]` (the `variable {L …}` block at lines 32–33 is not in this lemma's signature).

Hypotheses (Lean side):
- `(hn : 1 ≤ n)` — `n ≥ 1`, so that `n−1` and the digit-sum strictness make sense.

Conclusion (math): `p^{−(n−1)} ≤ ‖n!‖_p^{\,p−1}`, i.e. `v_p(n!) ≤ (n−1)/(p−1)`.

Conclusion (Lean): `(p : ℝ) ^ (-((n : ℤ) - 1)) ≤ ‖(n.factorial : ℚ_[p])‖ ^ (p - 1)`
(LHS is an integer `zpow` on `ℝ`; RHS exponent `p−1` is a `ℕ` `pow`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma (decomposition tag "E2"), not a `## Main results` entry and not named after a person. It is the technical denominator estimate feeding `norm_factorial_inv_pow_le` → the geometric decay bounds → summability of the `exp`/`log` series. (The *mathematical* fact behind it — Legendre's formula — is famous, but this rpow-free repackaging is the helper, not Legendre itself.)

(Note: literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is a multi-line `by` proof, lines 53–61.)

---

### PHASE 3 — Literature search (EXHAUSTIVE)

The concept the *statement* encodes is **Legendre's formula** for the p-adic
valuation of `n!` (equivalently de Polignac's formula), specialised to the
upper bound `v_p(n!) ≤ (n−1)/(p−1)` and transported to the norm. The proof's
mathematical content is entirely that classical inequality.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|----------------------|-------|
| 1 | WebSearch (specific form) | "p-adic valuation of factorial Legendre formula v_p(n!) = (n − s_p(n))/(p−1)" | yes | `v_p(n!) = Σ⌊n/p^k⌋ = (n − s_p(n))/(p−1)` | Wikipedia *Legendre's formula*; cut-the-knot *Legendre's Theorem*; arXiv 1907.11902. The `≤ (n−1)/(p−1)` bound is the immediate corollary (`s_p(n) ≥ 1` for `n ≥ 1`). |
| 2 | WebSearch (general / application form) | "p-adic norm of n! bound exponential convergence radius p^{−1/(p−1)}" | yes | `ord(n!) ≤ n/(p−1)`; gives `exp` radius `|x|_p < p^{−1/(p−1)}` | Thorne/Conrad p-adic analysis notes; MIT 18.785 PS10 (the p-adic log/exp problem); UChicago REU notes (Chen, Gupta); Wikipedia *p-adic exponential function*. This is precisely the use the AINTLIB file puts it to. |
| 3 | WebSearch (named-after / textbook aliases) | "Legendre formula factorial valuation Silverman elliptic curves IV.6.2 formal logarithm p-adic norm bound" | yes | Same bound; classical | Milne *Elliptic Curves*, Husemöller; the file's own docstring cites Cassels §12, Washington §5.1, RJW Lem 5.14; the sibling AINTLIB file cites **Silverman AEC IV.6.2** for the same `v_p(n!) ≤ (n−1)/(p−1)`. Also surfaced arXiv 2408.00353 "Bounds on the p-adic valuation of the factorial". |
| 4 | ChatGPT MCP | — | **n/a** | — | ChatGPT MCP server not configured in this environment (`mcp__chatgpt__*` tools absent on lookup). Recorded as n/a; the three WebSearches at different generality levels + Wikipedia fetch + nLab cover the standard-form question conclusively, since the result is a textbook classic with no formulation ambiguity. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` ; `ls refs/` | **n/a** | (no references dir; no `refs/` symlink) | Neither the project `references/` dir nor the gitignored `refs/` store is present in this checkout. Recorded n/a. The in-file docstring citations (RJW Lem 5.14, Cassels §12, Washington §5.1) substitute. |
| 6 | nLab | "p-adic exponential" / "Legendre formula valuation" | partial | confirms radius `p^{−1/(p−1)}` via `v_p(n!)` | nLab's *p-adic number* / exponential entries state the convergence radius via the factorial valuation; the bound itself is treated as standard, not given a separate page. |
| 7 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept (an elementary arithmetic inequality). |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry concept; Stacks has no p-adic-analysis valuation-of-factorial material. |
| 9 | MathOverflow / Math.SE | (covered transitively by #1–#3) | yes | `v_p(n!) ≤ (n−1)/(p−1)` ubiquitous | The bound and its use for the exp radius is standard Q&A fare; no variant or controversy. |
| 10 | recent arXiv (last 5y) | "Bounds on the p-adic valuation of the factorial" (2408.00353); "Legendre's formula and p-adic analysis" (1907.11902) | yes | refinements/surveys of the same formula | Modern papers refine constants / study `s_p(n)` finely, but the `(n−1)/(p−1)` upper bound is the baseline they start from — no newer "standard form" supersedes it. |

### Literature summary (Phase 3)

Concept identified as: **Legendre's formula** (a.k.a. de Polignac's formula) for the `p`-adic valuation of `n!`; the lemma is its corollary bound `v_p(n!) ≤ (n−1)/(p−1)`, transported to the norm and written rpow-free as `p^{−(n−1)} ≤ ‖n!‖_p^{\,p−1}`.
Sources agree on the standard form: **yes** — unanimous. Classical since Legendre 1830; no formulation ambiguity.
Most general standard form: `(p−1)·v_p(n!) = n − s_p(n)` (the exact identity), whence `v_p(n!) ≤ (n−1)/(p−1)` for `n ≥ 1` since `s_p(n) ≥ 1`.
Generality dimensions where the literature varies:
  - sharpness: identity (`= (n−s_p(n))/(p−1)`) vs. bound (`≤ (n−1)/(p−1)`) vs. coarse (`≤ n/(p−1)`). The lemma takes the middle one.
  - carrier of the conclusion: stated as a valuation inequality in ℤ/ℝ (the literature default) vs. a norm inequality in ℚ_p (this lemma's choice).
Disagreement with the literature: **none mathematically.** The literature states this on the *valuation* side; this lemma is a norm-side, rpow-free *repackaging* of it. That repackaging — not the mathematics — is what is project-specific.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): the valuation identity `(p−1)·v_p(n!) = n − s_p(n)`, with corollary bound `v_p(n!) ≤ (n−1)/(p−1)`.

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[Fact p.Prime]` | `p` prime | `p` prime | NO | Legendre's formula is intrinsically about a prime; `s_p`, `v_p` need it. |
| 2 | carrier `ℚ_[p]` | norm in `ℚ_[p]` | valuation in ℤ/ℝ | yes (the *valuation* form is what mathlib already has — see Phase 5) | The norm form is strictly *less* general than mathlib's valuation statement: it is `valuation form ∘ norm↔valuation bridge`. Going norm→valuation loses nothing and is what mathlib stores. |
| 3 | conclusion shape `p^{−(n−1)} ≤ ‖n!‖^{p−1}` | rpow-free `(p−1)`-power form | `v_p(n!) ≤ (n−1)/(p−1)` (a clean ℝ-division) | yes — the division form is cleaner and more general | The `^(p−1)` device exists only to dodge `Real.rpow`; it is an *engineering* specialisation that makes the statement **less** reusable, not more. Mathlib has `Real.rpow` and routinely uses it, so the division form would be the mathlib-idiomatic one. |
| 4 | `(hn : 1 ≤ n)` | `n ≥ 1` | `n ≥ 1` for the `(n−1)` bound | (coarser `n/(p−1)` drops it) | Needed for the `−1`; the coarser hypothesis-free bound exists (the sibling HasseWeil `padicValNat_factorial_div_le`) but is looser. Fine as is. |

#### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** — but *narrower in the wrong direction for a mathlib contribution*. The rpow-free `‖·‖^{p−1}` packaging (rows 2–3) is a deliberate downgrade of mathlib's existing cleaner valuation statement, undertaken to avoid `Real.rpow` inside this one project. It is not a generalisation opportunity; it is project-internal glue around a lemma mathlib already has.
Number of weakening opportunities found: 0 *toward mathlib* (the only "weakenings" — rows 2,3 — move toward the valuation/division form that **mathlib already stores**, i.e. they collapse the lemma into `NO-mathlib-has-it`-adjacent territory, not into a new contribution).
Proposed restatement: none for upstreaming — the genuinely-general statement (`v_p(n!) ≤ (n−1)/(p−1)`, or the exact Legendre identity) is **already in mathlib** (Phase 5). This lemma is the project's norm-side adapter of it.
Cost of restatement: n/a (no upstreaming target distinct from what mathlib has).

#### 4c. Modern-idiom check (Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses? | no | — | Already typeclass-driven (`Fact p.Prime`); nothing to bundle. |
| 2 | sequences/metric → filters/topological? | no | — | Pure arithmetic inequality; no limit notion in the statement. |
| 3 | construct an object → universal-property class? | no | — | No object constructed. |
| 4 | set-with-predicate → bundled substructure? | no | — | No substructure. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | **no, and the opposite** | — | The relevant weakening (norm→valuation) goes toward what mathlib already has; it is not a fresh generalisation. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general monoid/group? | no | — | `n : ℕ` is intrinsic (it's `n!`); `s_p`/`v_p` are ℕ-indexed by definition. |

#### 4c verdict
Modern idiom available: **no**. The only reformulation in play (drop the rpow-free `^(p−1)` device, write `v_p(n!) ≤ (n−1)/(p−1)` directly) is not a *modernisation that adds a new mathlib object* — it is precisely the form **mathlib already stores** (Phase 5). One-line reason: this is a classical scalar inequality whose general/idiomatic form already lives in mathlib; the local lemma is an rpow-avoidance adapter, not a Bourbaki-2.0 upgrade.

---

### PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths).

---

### PHASE 5 — Mathlib search

Search ran for **both** forms: the user's norm form `p^{−(n−1)} ≤ ‖n!‖_p^{\,p−1}`, and the literature-standard valuation form `v_p(n!) ≤ (n−1)/(p−1)` / `(p−1)·v_p(n!) < n`.

```
### Mathlib search-status: `PadicLFunctions.norm_factorial_le`

[A] Lean-Finder       n/a: Lean-Finder MCP not available in this environment.
[B] Loogle            n/a: lean_loogle MCP not available (tool lookup returned nothing).
[C] LeanSearch        n/a: lean_leansearch MCP not available.
[D] Grep mathlib src  EXHAUSTIVE — the authoritative method here. Findings below.
[E] Name pattern      n/a: lean_local_search MCP not available; substituted with targeted grep over mathlib (folded into [D]).
```

Grep findings ([D], over `.lake/packages/mathlib/Mathlib/`):

- **Legendre's formula — present, the exact math content:**
  `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:582`
  `sub_one_mul_padicValNat_factorial (n : ℕ) : (p - 1) * padicValNat p (n!) = n - (p.digits n).sum`  (**Legendre's Theorem**, the identity).
- **The strict bound the proof actually calls:**
  `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:591`
  `sub_one_mul_padicValNat_factorial_lt_of_ne_zero {n} (hn : n ≠ 0) : (p - 1) * padicValNat p n.factorial < n`. (This is the dependency `norm_factorial_le` imports — via `PadicLFunctions.Coefficients`/transitive mathlib import — and uses at line 58.)
- **Norm ↔ valuation bridge — present:**
  `Mathlib/NumberTheory/Padics/PadicNumbers.lean:1053` `Padic.norm_eq_zpow_neg_valuation {x : ℚ_[p]} : x ≠ 0 → ‖x‖ = (p:ℝ)^(-x.valuation)` and `:1078` `Padic.valuation_natCast (n) : valuation (n : ℚ_[p]) = padicValNat p n`. (Both used in the proof, lines 55.)
- **Norm-side factorial bound — ABSENT.** No lemma anywhere in mathlib bounds `‖(n.factorial : ℚ_[p])‖` (or any `‖n!‖_p`). Broad greps for `‖…factorial…ℚ_[p]`, `norm…Nat.factorial`, and `… ^ (p−1)` near `‖·‖` returned only the archimedean `Complex/Real` exponential files and unrelated `NormPow` derivative lemmas. The specific rpow-free shape `p^{−(n−1)} ≤ ‖n!‖^{p−1}` exists nowhere.
- **p-adic exponential — ABSENT.** Mathlib has no p-adic `exp`/`log` and no `p^{−1/(p−1)}` convergence-radius API (mathlib's `exp` in `Analysis/Normed/Algebra/Exponential.lean` is the archimedean Banach-algebra one). So there is no surrounding mathlib home that would want this exact norm-side helper.

Concluded: **"found building blocks"** — mathlib has the full mathematical content on the **valuation side** (`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, the Legendre identity) plus the norm↔valuation bridge (`Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`); the *norm-side rpow-free repackaging* in this exact form is not present, and is obtainable by composing those building blocks.

(Note: this is *not* `NO-mathlib-has-it`: mathlib does not have a lemma whose statement is `‖n!‖_p^{p−1} ≥ p^{−(n−1)}` that this follows from in ≤1 line — it has the *valuation* statement, and getting from there to the norm form requires the bridge + real-exponent monotonicity, i.e. a small composition. Hence the verdict turns on Phase 6.)

---

### PHASE 6 — Composition check (+ call-sites signal)

#### 6.0. Call sites — `PadicLFunctions.norm_factorial_le`

Internal use count: **1** (within PadicLFunctions, excluding the declaring line).
External-to-file callers: **0** distinct files (no other project, including HasseWeil, references it).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:75` | `… (norm_factorial_le p hn)` — fed straight into `inv_anti₀` inside `norm_factorial_inv_pow_le` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_factorial_le`?):
  - The sibling project HasseWeil **independently re-derives the same Legendre bound** on the *valuation/division* side: `projects/HasseWeil/HasseWeil/FormalGroup/PadicValFactorial.lean:45` `padicValNat_factorial_le : (padicValNat p n.factorial : ℝ) ≤ (n−1)/(p−1)` — same mathlib dependency `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, different (cleaner, rpow-using-division) packaging. This confirms the underlying fact is a recurring need, but each project wraps mathlib's lemma in its own ad-hoc shape. **Neither wrapper is shared; both consume the same mathlib lemma.**

**Signal:** K = 1 internal use, 0 external, sole consumer is the very next lemma (`norm_factorial_inv_pow_le`) which immediately inverts it. This is the "K = 1, possibly the wrong abstraction / could be inlined" pattern. Combined with the inline re-derivation of the same fact in HasseWeil (in a *different* shape), the wrapper is project-internal plumbing, not shared API.

#### 6a. Composition attempt

Can `norm_factorial_le` be derived from mathlib in ≤3 chained calls? The lemma's **own proof body** is the recipe and uses exactly the mathlib building blocks from Phase 5:

Attempt 1 (mirrors the existing proof, lines 53–61):
```lean
example {n : ℕ} (hn : 1 ≤ n) :
    (p : ℝ) ^ (-((n : ℤ) - 1)) ≤ ‖(n.factorial : ℚ_[p])‖ ^ (p - 1) := by
  rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.2 n.factorial_ne_zero),
      Padic.valuation_natCast, ← zpow_natCast _ (p - 1), ← zpow_mul]
  refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) ?_
  -- the math content: mathlib's Legendre strict bound
  have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : n ≠ 0)
  push_cast; omega   -- or: linarith [hcast] as in the original
```
  - Mathlib decls used: `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `zpow_le_zpow_right₀`, `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (the Legendre bound), plus `zpow_natCast`/`zpow_mul` rewrites and a final `omega`/`linarith`.
  - Result: **succeeds** (it is the existing proof).
  - Notes: this is a *short* derivation but it is **more than 3 clean "."-chained calls** — it needs two `zpow` rewrites to reshape exponents, one monotonicity lemma, and an arithmetic closer (`omega`/`linarith`) to pass from the strict ℕ inequality `(p−1)·v < n` to the real-exponent comparison `−(n−1) ≤ −((p−1)·v)`. So by the Phase 6b heuristics it is on the boundary: it is **not** a single `.trans`/`.symm`/one-function-call composition.

Attempt 2 (against the cleaner valuation form): if one first states `v_p(n!) ≤ (n−1)/(p−1)` (which is *itself* a 3-line composition of `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` + `omega` + a cast, exactly as HasseWeil's `padicValNat_factorial_le` does), then the norm form follows by the bridge + `Real.rpow`/`zpow` monotonicity. Still a multi-step glue, not a 1-call composition.

Conclusion: **COMPOSABLE** — the result is a short (≈4-mathlib-call) derivation gluing mathlib's Legendre bound to the p-adic norm↔valuation bridge with integer-power monotonicity. It crosses the "≤3 pristine chained calls" line only by the two exponent-reshaping rewrites and the arithmetic closer; per the verdict rules this still reads as *composable boilerplate around an existing mathlib theorem* rather than a new mathematical lemma. The decisive point: **the only non-mechanical ingredient is `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, which mathlib already provides** — everything else is the rpow-avoidance bookkeeping that exists solely to serve this project's `^(p−1)` convention.

---

## Verdict: `PadicLFunctions.norm_factorial_le`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the statement is **Legendre's formula**, classical since 1830, unanimous standard form `v_p(n!) ≤ (n−1)/(p−1)`. The lemma is its norm-side, rpow-free repackaging — no formulation novelty.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD**, but narrower in the *wrong direction* — the `‖·‖^{p−1}` device is a deliberate downgrade of the cleaner valuation/division form **that mathlib already stores**. Modern-idiom check: no new mathlib object; the "idiomatic" form is the one mathlib has.
- Mathlib search (Phase 5): the mathematical content is in mathlib as `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (Legendre) + the bridge `Padic.norm_eq_zpow_neg_valuation` / `Padic.valuation_natCast`; the **norm-side rpow-free shape is absent**, and there is no p-adic-exp home in mathlib that would want it.
- Composition check (Phase 6): **COMPOSABLE** — a ≈4-call glue (bridge + Legendre bound + `zpow` monotonicity + arithmetic closer); K = 1 internal use, 0 external; the same fact is independently re-wrapped in a *different* shape in HasseWeil, confirming it is per-project plumbing rather than shared API.

**Rationale:**

The mathematics here is Legendre's formula, and mathlib already has it in its
sharpest form (`sub_one_mul_padicValNat_factorial`, the exact identity, and the
strict corollary `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` that this
lemma actually invokes at line 58). What `norm_factorial_le` adds is *not*
mathematical content but a **format conversion**: it moves Legendre's bound from
the valuation side to the norm side and writes it rpow-free as
`p^{−(n−1)} ≤ ‖n!‖_p^{\,p−1}`, purely so the rest of `PadicExp.lean` can avoid
`Real.rpow` and the `p^{−1/(p−1)}` radius. That conversion is a short
composition of three things mathlib already provides — the Legendre bound, the
norm↔valuation bridge `Padic.norm_eq_zpow_neg_valuation`, and the natCast
valuation lemma `Padic.valuation_natCast` — glued with `zpow` monotonicity and
a one-line `omega`/`linarith`. It is not a new theorem in any mathlib-meaningful
sense; it is the kind of API-shaping boilerplate the `/cleanup` "no wrapper
lemmas" rule targets.

The `^(p−1)` packaging makes the lemma *less* reusable than mathlib's existing
valuation statement, so it is not a `YES-but-generalise-first` (the more general
form is already upstream, not a target to chase). It is not a clean
`NO-mathlib-has-it` either, because no single mathlib lemma has the norm-side
inequality that this follows from in ≤1 line — the derivation needs the bridge
plus real-power monotonicity. That places it squarely in
`NO-composable-from-mathlib`: keep it as a private, project-local helper
(exactly what it already is — used once, by the next lemma), but it should not
be proposed to mathlib. The call-site evidence reinforces this: it has a single
internal consumer and zero external ones, and the sibling HasseWeil project
re-derives the same Legendre bound in its own incompatible shape rather than
importing this — a textbook "wrong/ad-hoc abstraction, consumers bypass it"
signal.

**WHY not (refactor-actionable):**

Mathlib has the building blocks; `norm_factorial_le` is a thin norm-side adapter
around mathlib's Legendre inequality, justified only by this project's
rpow-avoidance convention.

Mathlib building blocks (qualified names + paths):
- `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` — `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:591` (the mathematical content: `(p−1)·v_p(n!) < n`).
- `Padic.norm_eq_zpow_neg_valuation` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:1053` (`‖x‖ = p^{−valuation x}`).
- `Padic.valuation_natCast` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:1078` (`valuation (n : ℚ_[p]) = padicValNat p n`).
- `zpow_le_zpow_right₀`, `zpow_mul`, `zpow_natCast` — exponent monotonicity / reshaping (Mathlib `Algebra/Order/GroupWithZero/...` and `Algebra/GroupPower/...`).

Composition sketch (the lemma's own proof, kept as project-local glue):
```lean
-- already exactly this in PadicExp.lean:53–61
rw [Padic.norm_eq_zpow_neg_valuation hf0, Padic.valuation_natCast,
    ← zpow_natCast _ (p - 1), ← zpow_mul]
refine zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le) ?_
have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : n ≠ 0)
-- cast hlt to ℤ and close with linarith
```

Call sites in our project (from Phase 6.0): **K = 1** (`PadicExp.lean:75`, inside `norm_factorial_inv_pow_le`).

Refactor plan: this is *not* a "delete and inline at K sites" case in the strong
sense, because the composition is ~4 mathlib calls (slightly over the pristine
≤3 bar) and is genuinely convenient as a one-line handle for its single
consumer. Concretely:
  1. **Do NOT propose to mathlib.** It carries no mathematical content beyond
     mathlib's Legendre lemma; a mathlib PR of `‖n!‖_p^{p−1} ≥ p^{−(n−1)}` would
     be rejected as a wrapper. (If mathlib ever gains a p-adic `exp`, the
     mathlib-shaped lemma to add then would be the **valuation/rpow** form
     `v_p(n!) ≤ (n−1)/(p−1)`, not this `^(p−1)` device.)
  2. **Keep it project-local**, ideally marked `private` (it has one internal
     caller, `norm_factorial_inv_pow_le`, and no external users). This is a
     `/cleanup`-lane action, not a mathlibable one.
  3. **Cross-project dedup opportunity (cleanup, not mathlib):** the same
     Legendre bound is independently wrapped at
     `projects/HasseWeil/.../PadicValFactorial.lean:45` (`padicValNat_factorial_le`,
     the cleaner `(n−1)/(p−1)` ℝ-form). A `Common/` home for "the ℝ-valued
     Legendre factorial bound" — stated once on the valuation side — could serve
     both, with each project deriving its own norm/rpow shape locally. That is a
     dedup ticket on `main`, not a mathlib contribution.

**Next action:** Do **not** open a mathlib PR. Treat as a `/cleanup`-lane item:
(a) consider marking `norm_factorial_le` `private` in `PadicExp.lean` (single
internal consumer); (b) file a cross-project dedup ticket to factor the shared
Legendre `v_p(n!) ≤ (n−1)/(p−1)` bound (currently duplicated between
PadicLFunctions and HasseWeil) into `Common/`, each project keeping its own
rpow-free / division presentation as a thin local adapter over mathlib's
`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`.

---

## Next step

Do **not** open a mathlib PR. Treat as a `/cleanup`-lane item: (a) consider marking `norm_factorial_le` `private` in `PadicExp.lean` (single internal consumer, zero external); (b) file a cross-project dedup ticket to factor the shared Legendre `v_p(n!) ≤ (n−1)/(p−1)` bound (duplicated between PadicLFunctions `norm_factorial_le` and HasseWeil `padicValNat_factorial_le`) into `Common/`, each project keeping its own rpow-free / division presentation as a thin local adapter over mathlib's `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`.
