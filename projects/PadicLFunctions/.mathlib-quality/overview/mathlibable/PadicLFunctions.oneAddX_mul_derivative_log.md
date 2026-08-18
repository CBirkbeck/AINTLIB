# `/mathlibable` report — `PadicLFunctions.oneAddX_mul_derivative_log`

**Final verdict: `YES-add-as-is`** (with one naming caveat — re-namespace to `PowerSeries` and rename to the mathlib `X`-convention before opening the PR; this is a `/cleanup`-time mechanical fix, not a generalisation).

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); **reasoned from source**. The proof body is `rw [deriv_log]; ext n; rw [coeff_one]; match … ; ring` over mathlib lemmas that all resolve in source — no `sorry`.
- decl `PadicLFunctions.oneAddX_mul_derivative_log`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:470`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp`/`log` as formal/convergent power series over a nonarchimedean ℚ_[p]-algebra; this theorem is in `section Inversion`, the formal-identity layer feeding `exp(log(1+X)) = 1+X`.

---

### Statement (Phase 1)

`PadicLFunctions.oneAddX_mul_derivative_log` is a **theorem** stating the following:

> Over any commutative ℚ-algebra `A`, the formal power series identity
> `(1 + X) · D(log(1+X)) = 1` holds in `A⟦X⟧`, where `log(1+X) = X − X²/2 + X³/3 − ⋯`
> is mathlib's `PowerSeries.log` and `D = d⁄dX` is mathlib's formal derivation
> `PowerSeries.derivative`.

Equivalently: **the formal derivative of `log(1+X)` is the multiplicative inverse of `1+X`**, i.e. `D(log(1+X)) = 1/(1+X) = ∑ (−1)ⁿ Xⁿ`. This is the formal-power-series form of the calculus fact `d/dx log(1+x) = 1/(1+x)`.

Variables / typeclasses involved (Lean side):
- `A : Type*` — the coefficient ring (carrier of the power-series ring `A⟦X⟧`).
- `[CommRing A]` — `A` is a commutative ring.
- `[Algebra ℚ A]` — `A` is a ℚ-algebra (required: `PowerSeries.log` divides by `n`, so the rationals must embed).

Hypotheses (Lean side): none beyond the typeclasses.

Conclusion (math): `(1+X)·D(log(1+X)) = 1` in `A⟦X⟧`.

Conclusion (Lean): `(1 + PowerSeries.X) * (d⁄dX A (PowerSeries.log A)) = 1`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline, treated as BIG for framing).
Reason: It is a *named formal identity* — the formal-power-series form of `d/dx log(1+x) = 1/(1+x)` — and it is the engine behind a genuinely canonical result (`exp(log(1+X)) = 1+X`, the very example mathlib's own `Derivative.lean` docstring cites, line 22). Not a person-named theorem, but a textbook-standard FPS identity, not project bookkeeping.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the report's framing only.)

### One-line check (Phase 2b)

Body line count: ~9 substantive lines (`rw [deriv_log]`, `ext n`, `coeff_one`, a `match` with a `simp`, and an `add_mul/map_add/coeff_succ_X_mul/coeff_mk/pow_succ/ring` chain on the successor branch).
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`. The Phase-2b exemption table is skipped.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "derivative of log(1+X) formal power series equals 1/(1+X) geometric series identity"                  | yes  | `D(log(1+X)) = ∑(−1)ⁿXⁿ = 1/(1+X)` | uwaterloo CO430 FPS notes, arXiv:2205.00879 "An invitation to formal power series", planetmath; unanimous |
|  2 | WebSearch (general form)         | "formal power series logarithm derivative (1+X) D log = 1 invertibility ring"                          | yes  | `log(1+X)` reverse of `exp(X)−1`; `exp(log(1+X))=1+X`; units of `R[[X]]` ⇔ invertible constant coeff | Wikipedia "Formal derivative", "Formal power series"; `1+X` is a unit so `(1+X)·D(log)=1` is the inverse statement |
|  3 | WebSearch (named-after / aliases)| "log(1+x) formal power series over Q-algebra commutative ring standard generality derivation"          | yes  | `log α = ∑ (−1)ⁿ⁻¹/n·(α−1)ⁿ` for `α∈1+xR[[x]]`, R ⊇ ℚ | Confirms the **ℚ-algebra** hypothesis cluster is exactly the standard generality; angyansheng CA-II notes, "Formal Rings" arXiv:1902.03665 |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution)                                          | n/a  | —                   | **ChatGPT MCP not authenticated** on this machine (`~/.claude/mcp-needs-auth-cache.json` present, no live server). Substituted query #3 above to cover the generality/historical question; recorded n/a per protocol with reason. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                    | n/a  | —                   | Directory absent; `refs/PadicLFunctions/` symlink also absent. Recorded n/a with reason. |
|  6 | nLab                             | "nLab formal power series ring derivation logarithm exponential Hurwitz"                                | yes  | `log(exp X)=X`, `exp(log(1+X))=1+X`; FPS derivation via dual numbers | ncatlab.org/nlab/show/power+series; treats `exp`/`log` as mutually inverse FPS, the inverse-derivative identity is implicit |
|  7 | nCatLab (if categorical)         | (covered by #6 — nLab is nCatLab)                                                                      | n/a  | —                   | Not a higher-categorical concept; the relevant nLab page is the one hit in #6. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                   | Not an algebraic-geometry concept; it is a formal-power-series algebra identity. No Stacks tag. |
|  9 | MathOverflow / Math.StackExchange| (covered by #1–#3 result pages: Physics Forums / Study.com / Cornell power-series notes)               | yes  | same as #1          | Q&A pages restate `d/dx ln(1+x)=1/(1+x)` and its series form; nothing more general than #1–#3. |
| 10 | recent arXiv (last 5 years)      | "An invitation to formal power series" (arXiv:2205.00879, 2022); "Formal Rings" (arXiv:1902.03665)     | yes  | same standard form, ℚ-algebra generality | Modern treatments confirm: no generalisation beyond commutative ℚ-algebra; the identity is stated as-is. |

#### Literature summary (Phase 3)

Concept identified as: **the formal-derivative identity for the formal logarithm** — `D(log(1+X)) = 1/(1+X)`, equivalently `(1+X)·D(log(1+X)) = 1`, the FPS form of `d/dx log(1+x) = 1/(1+x)`.
Sources agree on the standard form: **yes** — unanimous across FPS lecture notes, Wikipedia, planetmath, nLab, and recent arXiv surveys.
Most general standard form: over any **commutative ℚ-algebra** (equivalently a commutative ring containing ℚ): `log(1+X) := ∑_{n≥1} (−1)ⁿ⁺¹/n · Xⁿ`, and its formal derivative is the alternating geometric series `∑_{n≥0} (−1)ⁿ Xⁿ`, which is exactly the multiplicative inverse of `1+X`. Hence `(1+X)·D(log(1+X)) = 1`.
Generality dimensions where the literature varies:
  - Coefficient ring: ranges from `ℚ` itself up to any commutative ℚ-algebra; **the most general is "commutative ring ⊇ ℚ"**, which is precisely `[CommRing A] [Algebra ℚ A]`. (Below ℚ-algebra the series is undefined — `1/n` needs ℚ.)
  - Substitution form: some texts state it for `log(1+X)` at `X`, some for `log f` at a power series `f` with `f(0)=1`; the `X`-form is the primitive one and the general `f`-form is its substitution (mathlib's `logOf`).
Disagreement with the literature: **none.** The user's form `(1+X)·D(log A) = 1` over `[CommRing A] [Algebra ℚ A]` *is* the maximally general standard form.

---

### Generality analysis — `PadicLFunctions.oneAddX_mul_derivative_log` (Phase 4)

Literature-standard form (from Phase 3): `(1+X)·D(log(1+X)) = 1` over any commutative ℚ-algebra.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `A : Type*` | arbitrary type | the coefficient ring | — | maximally general (any type carrying the structure) |
| 2 | `[CommRing A]` | commutative ring | commutative ring | NO | `PowerSeries.log` and `mk_one_mul_one_sub_eq_one` are stated for `CommRing`; the derivative-Leibniz proof needs commutativity. This matches mathlib's `PowerSeries.log` signature exactly. |
| 3 | `[Algebra ℚ A]` | ℚ-algebra | ring containing ℚ | NO | **Essential** — `log` divides by `n` (`(-1)^(n+1)/n`), so the rationals must embed. Phase 3 #3 confirms ℚ-algebra is the literature's generality floor. Mathlib's `PowerSeries.log` carries the identical `[Algebra ℚ A]`. |

#### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: **K = 0**.
Proposed restatement: none (already at the literature-standard generality, and at *exactly* mathlib's `PowerSeries.log` typeclass cluster `[CommRing A] [Algebra ℚ A]`).
Cost of restatement: n/a.

#### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses? | no | — | Already fully typeclass-based (`[CommRing A] [Algebra ℚ A]`); no bundled-hypothesis preamble to dissolve. |
|  2 | sequences/metric → filters/nets? | no | — | Purely algebraic FPS identity; no convergence/topology to filter-ise. The `d⁄dX` derivation is already the formal (limit-free) one. |
|  3 | construct object → universal property? | no | — | It's an identity about an existing object, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure involved. |
|  5 | vector-space/metric/field-specific → modules/(semi)ring? | no | — | Already at `CommRing`+`Algebra ℚ`; that is the correct floor (Phase 4 row 3). Cannot weaken without losing `1/n`. |
|  6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | — | The only "index" is the power-series exponent `ℕ`, intrinsic to `PowerSeries`. |

#### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: the declaration is already stated in mathlib's contemporary `PowerSeries`/`Derivation` idiom — it uses `PowerSeries.log`, the `d⁄dX = PowerSeries.derivative` bundled `Derivation`, and the exact `[CommRing A] [Algebra ℚ A]` typeclass cluster mathlib's `Log.lean` uses. There is no more-modern reformulation; it *is* the modern form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.oneAddX_mul_derivative_log` (Phase 5)

Five-method search (read `references/mathlib-search.md` shape). Searched **both** the user's form `(1+X)·D(log)=1` and the literature-standard form (the inverse-of-`(1+X)` / alternating-geometric identity).

```
[A] Lean-Finder       n/a — Lean-Finder MCP not available on this machine; substituted [D]+[E] grep over the pinned mathlib tree (authoritative for "is it there").
[B] Loogle            type pattern `(1 + PowerSeries.X) * _ = 1`, `PowerSeries.derivative _ (PowerSeries.log _) = _`
                                                     — no hit (Loogle MCP unavailable; emulated by structural grep [D], which is exact against the pin)
[C] LeanSearch        "derivative of formal log times (1+X) equals one"  — no hit (MCP unavailable; covered by [D]/[E] + Phase 3 literature anchor)
[D] Grep mathlib src  `(1 + X)`, `(1 + PowerSeries.X)`, `deriv_log`, `derivative.*log`, `mk_one_mul`, `invOneSub`, `1 / (1 + X)`, alternating-geometric, over `.lake/packages/mathlib/Mathlib/`
                                                     — see findings below
[E] Name pattern      `one_add_X_mul`, `oneAddX`, `mul_deriv_log`, `derivative_log_eq`, `invOneAdd`  — no hit in mathlib
```

**Findings (the load-bearing part):**

- Mathlib **HAS the entire surrounding API, in the same `PowerSeries` namespace**, and the user's proof calls it directly:
  - `PowerSeries.log` — `Mathlib/RingTheory/PowerSeries/Log.lean:42` (identical def to what the theorem is about).
  - `PowerSeries.deriv_log : d⁄dX A (log A) = mk fun n ↦ algebraMap ℚ A ((-1)^n)` — `Log.lean:67`. **The user's proof opens with `rw [deriv_log]`.** Its docstring (`Log.lean:31-32, 66`) literally asserts the math fact *"the geometric series `∑(−1)ⁿ·Xⁿ = 1/(1+X)`"* — **but only proves the derivative formula, not the multiplicative-inverse identity.**
  - `PowerSeries.derivative` / `d⁄dX` notation — `Mathlib/RingTheory/PowerSeries/Derivative.lean:102,109`.
  - `PowerSeries.exp`, `PowerSeries.derivative_exp` — `Exp.lean:69`; `PowerSeries.derivative_subst` — `Derivative.lean:184`.
  - Sibling identity `PowerSeries.mk_one_mul_one_sub_eq_one : (mk 1) * (1 - X) = 1` — `WellKnown.lean:77` (the **`(1−X)` non-alternating** geometric-inverse identity).

- The **exact identity `(1 + X) · D(log) = 1` is NOT in mathlib.** Confirmed:
  - `grep '(1 + X)' … | grep '= 1\|mul'` over all of `Mathlib/` → **zero** hits for any `(1+X)·… = 1`.
  - `grep -i '1/(1+x)\|invOneAdd\|alternating geometric'` over all of `Mathlib/` → only the *prose docstring* of `deriv_log` (`Log.lean:32,66`) — no theorem.
  - Mathlib has the `(1−X)` version (`mk_one_mul_one_sub_eq_one`) but **no `(1+X)` alternating-geometric inverse** and **no `(1+X)·D(log)=1`** anywhere.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard inverse form). Mathlib has every building block *and a named sibling* (`mk_one_mul_one_sub_eq_one`), and `deriv_log`'s docstring promises the fact, **but the identity itself is missing.**

---

### Call sites — `PadicLFunctions.oneAddX_mul_derivative_log` (Phase 6.0)

Internal use count: **K = 2** (within the project, NOT counting the declaring file → 0; both uses are *in* the declaring file `PadicExp.lean`).
External-to-file callers: **0 distinct files** (both call sites are inside `PadicExp.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| PadicExp.lean:495 | `rw [hDF, ← mul_assoc, mul_comm (1 + PowerSeries.X) F, mul_assoc, oneAddX_mul_derivative_log, mul_one]` — discharges the recursion `(1+X)·D F = F` in `exp_subst_log` |
| PadicExp.lean:548 | `rw [oneAddX_mul_derivative_log, ← coe_substAlgHom hg, map_one]` — discharges `((1+X)·D(log)).subst(exp−1) = 1` in `log_subst_exp_sub_one` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - `ResidueZeta.lean`, `ValuesAtOne.lean`, `MeasureR/FormalPsi.lean` each prove **analogous but different** `one_add_mul_derivative_*` lemmas (for `FtildeA`, `logSeriesAt`, `phiSeries`, … — substituted/branch-specific variants), not a re-derivation of *this* `X`-primitive identity. They are downstream specialisations that would each rest on this primitive. So: the primitive itself is used twice in-file; its *pattern* recurs across ≥3 other files as bespoke variants — a strong signal the `X`-form is the right reusable base.

### Composition check (Phase 6)

Can `oneAddX_mul_derivative_log` be derived from mathlib in ≤3 chained calls?

Attempt 1: `rw [deriv_log]` reduces the goal to `(1 + X) * (mk fun n ↦ algebraMap ℚ A ((-1)^n)) = 1` — the **alternating** geometric-inverse identity. Then hope to close with `mk_one_mul_one_sub_eq_one`.
  - Mathlib decls used: `PowerSeries.deriv_log`, `PowerSeries.mk_one_mul_one_sub_eq_one`.
  - Result: **fails.** `mk_one_mul_one_sub_eq_one` is `(mk 1)·(1 − X) = 1` — the **non-alternating** series times `(1 − X)`. Our series is `mk (fun n ↦ (−1)ⁿ)` (alternating) times `(1 + X)`. They are not the same lemma; bridging requires substituting `X ↦ −X` and there is no mathlib lemma packaging that for `mk`-series. No single mathlib call closes `(1+X)·(alternating geom) = 1`.

Attempt 2: prove `(1+X)·mk(fun n ↦ (−1)ⁿ) = 1` directly by coefficients.
  - This is exactly the user's proof body: `ext n; rw [coeff_one]; match n with | 0 => simp | k+1 => rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk, if_neg …]; simp only [map_pow, map_neg, map_one]; rw [pow_succ]; ring`. That is **~8 lines of genuine coefficient reasoning** (per-coefficient case split + `coeff_succ_X_mul` + `pow_succ` + `ring`), not a chain of ≤3 named-lemma calls.

Conclusion: **NOT-COMPOSABLE.** Mathlib has the building blocks and a *sibling* identity, but assembling `(1+X)·D(log) = 1` from them is a real proof (the per-coefficient alternating-cancellation argument), not a ≤3-call composition.

---

## Verdict: `PadicLFunctions.oneAddX_mul_derivative_log`

**Category:** `YES-add-as-is`

**Evidence:**
- Literature search (Phase 3): unanimous standard form `(1+X)·D(log(1+X)) = 1` = `D(log(1+X)) = 1/(1+X)`; maximally general over commutative ℚ-algebras; the user's form *is* the standard form (10 channels; ChatGPT-MCP n/a with reason, substituted; local refs n/a).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (K=0 weakenings; typeclasses `[CommRing A] [Algebra ℚ A]` are exactly mathlib's `PowerSeries.log` cluster and the literature floor). Modern-idiom check: no further modernisation — already in mathlib's `PowerSeries`/`Derivation` idiom.
- Mathlib search (Phase 5): **not in mathlib.** Mathlib has the entire surrounding API in the same namespace (`PowerSeries.log`, `deriv_log`, `derivative`, the sibling `mk_one_mul_one_sub_eq_one`), and `deriv_log`'s docstring asserts "`= 1/(1+X)`" in prose — but the inverse identity `(1+X)·D(log)=1` itself is absent.
- Composition check (Phase 6): **NOT-COMPOSABLE** — `deriv_log` + `mk_one_mul_one_sub_eq_one` do not chain (alternating `(1+X)` vs non-alternating `(1−X)`); closing the goal needs the ~8-line per-coefficient proof.

**Rationale:**

This is the formal-power-series statement that *the derivative of `log(1+X)` is the multiplicative inverse of `1+X`* — `(1+X)·D(log(1+X)) = 1`. Mathlib already contains the precise neighbourhood this belongs to: `Mathlib/RingTheory/PowerSeries/Log.lean` defines `PowerSeries.log`, proves `deriv_log` (that `D(log) = ∑(−1)ⁿXⁿ`), and its `deriv_log` docstring even *names the target fact in prose* — "the geometric series `∑(−1)ⁿ·Xⁿ = 1/(1+X)`" — without ever proving the multiplicative-inverse identity. Mathlib also has the exact non-alternating sibling, `mk_one_mul_one_sub_eq_one : (mk 1)·(1−X) = 1` (`WellKnown.lean:77`). So the gap is concrete and named: mathlib has `(1−X)·(geom) = 1` and asserts `D(log) = 1/(1+X)` rhetorically, but is missing the `(1+X)·D(log) = 1` theorem that ties the two together. The form is at the maximally general / mathlib-canonical level already (`[CommRing A] [Algebra ℚ A]`, matching `PowerSeries.log` verbatim), so there is nothing to generalise — hence `YES-add-as-is`, not `YES-but-generalise-first`. It is not composable: `deriv_log` + `mk_one_mul_one_sub_eq_one` fail to chain because one series is alternating over `1+X` and the other non-alternating over `1−X`, with no mathlib `X ↦ −X` bridge for `mk`-series; the user's proof does a genuine ~8-line per-coefficient cancellation that is a proof, not a ≤3-call composition.

WHY add it (REQUIRED — refactor-actionable detail):
- **New mathematical content:** the theorem `(1+X)·D(log(1+X)) = 1` — i.e. `D(log(1+X))` is the inverse of `1+X` in `A⟦X⟧`. Mathlib's `PowerSeries.deriv_log` stops at *computing* the derivative as `mk(fun n ↦ (−1)ⁿ)`; it never closes the loop to the inverse identity, even though its docstring claims it. This theorem is the missing closure.
- **The specific gap (named, not "searched and didn't find"):** `Mathlib/RingTheory/PowerSeries/Log.lean:31-32` and `:66` — the `deriv_log` docstring asserts `∑(−1)ⁿXⁿ = 1/(1+X)` as a comment but the file contains **no theorem** to that effect; `Mathlib/RingTheory/PowerSeries/WellKnown.lean:77` has only the `(1−X)` analogue (`mk_one_mul_one_sub_eq_one`). The `(1+X)`-derivative-inverse identity has no theorem anywhere in `Mathlib/` (grep of `(1 + X) … = 1` over the whole tree → 0 hits). This theorem fills exactly that documented-but-unproven gap and is the natural lemma to live immediately after `deriv_log`.
- **How it composes with mathlib's existing API:** it is the missing link that powers `exp(log(1+X)) = 1+X` — *the canonical example mathlib's own `Derivative.lean` docstring advertises* ("one can easily prove the power series identity `exp(log(1+X)) = 1+X` by differentiating twice", `Derivative.lean:21-22`). With this lemma plus `derivative_exp` and `derivative_subst` (both already in mathlib), `exp(log(1+X)) = 1+X` and `log(1+(exp−1)) = X` follow by the `derivative.ext` route (mathlib's `Derivative.lean:139`). The project's `exp_subst_log` (PadicExp.lean:487) and `log_subst_exp_sub_one` (PadicExp.lean:540) are exactly those two corollaries — strong candidates to ship to mathlib alongside, since mathlib's docstring already promises them.

Proposed mathlib location:    `Mathlib/RingTheory/PowerSeries/Log.lean` (immediately after `deriv_log`, line 67).
Proposed PR title:            "feat(RingTheory/PowerSeries): add `(1+X)·D(log) = 1` (formal `1/(1+X)`)"
PR grouping:                  Ship with the two corollaries it unblocks — the project's `exp_subst_log` (`exp(log(1+X)) = 1+X`) and `log_subst_exp_sub_one` (`log(1+(exp−1)) = X`), which mathlib's `Derivative.lean` docstring explicitly advertises. Assess each of those via `/mathlibable` first; if they come back YES, one PR adding `Log.lean`'s `exp(log(1+X)) = 1+X` cluster is the right grain.
Pre-PR checklist before opening:
  - [ ] **Rename + re-namespace (required at `/cleanup`):** move into `namespace PowerSeries` and rename to mathlib's `X`-convention — e.g. `one_add_X_mul_deriv_log` (cf. existing `mk_one_mul_one_sub_eq_one`, `coeff_succ_X_mul`, `derivative_X`). Drop the camelCase `oneAddX`. This is mechanical (statement unchanged), so it stays `YES-add-as-is`, not `YES-but-generalise-first`.
  - [ ] `/generalise oneAddX_mul_derivative_log` — confirm no weakening below `[CommRing A] [Algebra ℚ A]` (Phase 4 says none; `log` needs ℚ).
  - [ ] `/cleanup PadicExp.lean oneAddX_mul_derivative_log` — full audit; the proof (`match` + `coeff_succ_X_mul` + `ring`) is already idiomatic and short.
  - [ ] Pick a reviewer from recent `Mathlib/RingTheory/PowerSeries/` commits (the `Log.lean`/`Exp.lean` files are 2026-authored by Ralf Stephan — a natural reviewer).

---

## Next step

Open a mathlib PR adding `(1+X)·D(log) = 1` to `Mathlib/RingTheory/PowerSeries/Log.lean` immediately after `deriv_log`. First re-namespace into `PowerSeries` and rename to `one_add_X_mul_deriv_log` (mathlib `X`-convention), run `/generalise` (expected: no weakening — `[CommRing A] [Algebra ℚ A]` is the floor) and `/cleanup` on it, and consider grouping the PR with the two corollaries it unblocks (`exp(log(1+X)) = 1+X` and `log(1+(exp−1)) = X`) that mathlib's `Derivative.lean` docstring already advertises.
