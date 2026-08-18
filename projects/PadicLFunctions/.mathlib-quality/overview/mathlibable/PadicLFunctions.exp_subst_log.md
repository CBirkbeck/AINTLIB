# `/mathlibable` report — `PadicLFunctions.exp_subst_log`

**Final verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING — the
`ℚ_[p]` form is a needless specialisation of a standard identity that holds, with
the *same proof*, over any `[CommRing A] [Algebra ℚ A]`).

---

### Baseline (Phase 0)

- lake build:               not re-run; reasoned from source (per task BUILD NOTE — build is stale/slow here). Declaration and all dependencies read directly from source.
- decl `PadicLFunctions.exp_subst_log`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:487`
- kind:                      theorem
- has sorry:                 no (proof is complete; uses only mathlib + the project's own `oneAddX_mul_derivative_log`)
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14); convergence on the open ball, isometry, and `exp`/`log` inversion; the formal-power-series identities in the `Inversion` section feed `padicExp_padicLog`.

---

### Statement (Phase 1)

`PadicLFunctions.exp_subst_log` is a **theorem** stating the following:

> Over the formal power series ring `ℚ_[p]⟦X⟧`, substituting the logarithmic
> power series `log(1+X) = X − X²/2 + X³/3 − ⋯` into the exponential power series
> `exp = ∑ Xⁿ/n!` returns `1 + X`. In symbols, `exp ∘ log(1+·) = 1 + X`, i.e.
> `exp(log(1+X)) = 1 + X` as a formal identity.

This is the formal-power-series statement that `exp` and `log(1+·)` are mutually
inverse (one of the two inverse directions; the companion direction is the next
theorem in the file, `log_subst_exp_sub_one`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — only used to make sense of `ℚ_[p]`; **plays no role in the proof**.
- The objects `exp ℚ_[p]` and `PowerSeries.log ℚ_[p]` are **mathlib's** `PowerSeries.exp` (`Mathlib/RingTheory/PowerSeries/Exp.lean:48`) and `PowerSeries.log` (`Mathlib/RingTheory/PowerSeries/Log.lean:42`), specialised to base ring `ℚ_[p]`.

Hypotheses (Lean side): none beyond the ambient `ℚ_[p]`.

Conclusion (math): `exp(log(1+X)) = 1 + X` in `ℚ_[p]⟦X⟧`.

Conclusion (Lean): `(exp ℚ_[p]).subst (PowerSeries.log ℚ_[p]) = 1 + PowerSeries.X`.

**Proof shape** (read from source, `PadicExp.lean:487–535`): set `F := exp.subst(log)`;
show `D F = F · D(log)` by `derivative_subst` + `derivative_exp`; combine with the
project helper `oneAddX_mul_derivative_log` (`(1+X)·D(log)=1`) to get the ODE
`(1+X)·D F = F`; compute `constantCoeff F = 1` via `constantCoeff_subst`; read off
`coeff 1 F = 1`; then a coefficient recursion `coeff(m+2) F · (m+2) = −m · coeff(m+1) F`
forces `coeff(k+2) F = 0` for all `k` (dividing by the nonzero nat-casts `m+2, k+3`);
finally `ext n` matches `1 + X` coefficientwise. **No norm, ultrametric, completeness,
summability, or any `ℚ_[p]`-specific fact is used** — verified by grep over the proof
body (the only `norm`-token is the tactic `norm_num`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a named fundamental formal-power-series identity (exp/log mutual
inverse) — exactly the kind of result the literature names and that mathlib's own
`Derivative.lean` header advertises as a motivating example. Listed in the module
docstring's mathematical narrative (the `Inversion` section / RJW Lem 5.14 route).

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is for framing only.)

### One-line check (Phase 2b)

Body line count: ~40 substantive lines (multi-line coefficient-recursion proof).
One-liner verdict: **n/a — kind is theorem, not def.** Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `formal power series identity exp(log(1+X)) = 1+X composition inverse formal group` | yes | `exp(log(1+z)) = 1+z`, provable by formal chain-rule | Identified as "a fundamental formal power series identity… proven using only formal arguments, particularly the chain rule." Central to formal group theory. |
| 2 | WebSearch (general form) | `exponential logarithm formal power series mutually inverse characteristic zero proof differentiation` | yes | `exp = ∑ zⁿ/n!`, `log(1+z) = ∑ (−1)ⁿ⁺¹/n zⁿ`, **inverses over any char-0 ring** | "In characteristic zero the formal exp and log are equipped on formal power series algebras and are inverses of one another." Generality = char 0 / ℚ-algebra, NOT ℚ_[p]. |
| 3 | WebSearch (named-after / aliases) | `nLab formal power series exponential logarithm inverse Q-algebra characteristic zero` | yes | Same; "exp of an element with zero constant term, log of an element with constant term 1, inverse to each other" | Confirms the precise hypotheses (zero const. coeff for the inner series), char-0 framing. |
| 4 | ChatGPT MCP | "Standard form + generality + historical evolution of exp(log(1+X))=1+X as a formal identity" | n/a | — | **ChatGPT MCP is not configured in this environment** (no `chatgpt`/`openai` MCP tool surfaced in the deferred-tool list). Recorded n/a per the skill's documented WebSearch+nLab+Stacks fallback; the four WebSearch queries + nLab fetch more than cover the standard-form question. |
| 5 | Local references | `ls`/grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | n/a | (no references dir) | Both `projects/PadicLFunctions/.mathlib-quality/references/` and the `refs/` symlink are absent in this checkout — recorded n/a. (The module docstring cites RJW Lem 5.14, Cassels §12, Washington §5.1 as the human references.) |
| 6 | nLab | `power+series` page fetched | partial | nLab "power series" covers substitution/invertibility but the fetched excerpt did not contain the exp/log inverse statement explicitly | Page exists; relevant section not in the returned markdown. Char-0 inverse statement corroborated by channels 2,3,9 instead. |
| 7 | nCatLab (categorical) | — | n/a | — | n/a — this is a concrete algebraic identity in `R⟦X⟧`, not a categorical/higher-categorical concept. No 1-categorical statement to lift. |
| 8 | Stacks Project (alg geom) | — | n/a | — | n/a — not an algebraic-geometry / scheme-theoretic concept; it is an identity in the formal-power-series ring over a ℚ-algebra. |
| 9 | MathOverflow / Math.StackExchange | `"exp(log(1+X))=1+X" OR "log(1+(e^X-1))=X" formal power series inverse exp log Q-algebra` | yes | `(1+x)^λ = exp(λ log(1+x))` standard; `exp(log(1+X))=1+X` and `log(1+(eˣ−1))=X` are "consequences of the standard inverse relationships… over commutative rings containing ℚ" | Pins the generality precisely: **commutative rings containing ℚ** = `[CommRing A] [Algebra ℚ A]`. |
| 10 | recent arXiv (last 5 years) | (same search; surfaced) `arxiv.org/pdf/2205.00879` "An invitation to formal power series"; `arxiv.org/pdf/1201.4023` "Formal group exponentials… Lubin–Tate" | yes | Canonical modern treatments; `exp_{F_P}(X)=exp(X)−1`, `log_{F_P}(X)=log(X+1)` for the multiplicative formal group over ℚ_p | Confirms the ℚ_p case is one *instance* of the general char-0 identity; the general statement is the standard one. |

**Protocol pass:** WebSearch ran 4 distinct queries across generality levels (specific
form #1, most-general/char-0 form #2, named-after/nLab #3, MathOverflow form #9);
nLab fetched; Stacks/nCatLab recorded n/a with reasons; arXiv surfaced canonical
sources; local refs + ChatGPT MCP recorded n/a with reasons (both genuinely
unavailable here). The standard-form question is answered conclusively.

### Literature summary (Phase 3)

Concept identified as: **the formal exp/log mutual-inverse identity** — `exp(log(1+X)) = 1 + X` as formal power series.
Sources agree on the standard form: **yes**.
Most general standard form: over **any commutative ring containing ℚ** (equivalently `[CommRing A] [Algebra ℚ A]`, since `Algebra ℚ A` makes `A` a char-0 ring), with `exp = ∑ Xⁿ/n!` and `log(1+X) = ∑ (−1)ⁿ⁺¹/n Xⁿ`, the identity `exp(log(1+X)) = 1 + X` holds, proved purely formally (differentiate: both sides satisfy `(1+X)·D F = F` with `F(0) = 1`).
Generality dimensions where the literature varies:
  - Base ring: literature states it for **any char-0 ring / ℚ-algebra** (most general: commutative ring containing ℚ). The Lean form fixes the base ring to `ℚ_[p]` — strictly narrower, with no mathematical justification (the ℚ_[p] choice is purely because the surrounding file is about p-adic analysis).
Disagreement with the literature: the literature uses the **general ℚ-algebra base ring**; the Lean form specialises to `ℚ_[p]`.

---

### Generality analysis — `PadicLFunctions.exp_subst_log`

Literature-standard form (from Phase 3): `exp(log(1+X)) = 1 + X` over any `[CommRing A] [Algebra ℚ A]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | Base ring fixed to `ℚ_[p]` (via `p : ℕ`, `[Fact p.Prime]`) | the p-adics `ℚ_[p]` | arbitrary `[CommRing A] [Algebra ℚ A]` | **yes** | The proof uses ONLY: `derivative_subst`, `derivative_exp`, `constantCoeff_subst`, `coeff_succ_X_mul`, `coeff_derivative`, `oneAddX_mul_derivative_log`, and nat-cast nonzeroness in the coefficient recursion. Every one of these is available for general `[CommRing A] [Algebra ℚ A]` (the subst/derivative API is stated for `[CommRing A]`; `exp`/`log`/`oneAddX_mul_derivative_log` for `[CommRing A] [Algebra ℚ A]`). The nat-cast nonzeroness (`(m:A)+2 ≠ 0`, `(k:A)+3 ≠ 0`) follows from `CharZero A`, which mathlib supplies automatically for a ℚ-algebra via `algebraRat.charZero` (`Mathlib/Algebra/CharP/Algebra.lean:162`). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **1** (base ring `ℚ_[p]` → `[CommRing A] [Algebra ℚ A]`)

Proposed restatement (mathlib-idiomatic location `PowerSeries` namespace):

```lean
theorem PowerSeries.exp_subst_log (A : Type*) [CommRing A] [Algebra ℚ A] :
    (exp A).subst (log A) = 1 + X := by
  ... -- the existing proof, with ℚ_[p] replaced by A throughout
```

Cost of restatement: **CHEAP — mechanical rewrite.** The proof is copied verbatim
with `ℚ_[p] ↦ A`; the only steps that touch the base ring are the recursion's
`(mul_eq_zero.mp h).resolve_right (by norm_num)` / `.resolve_right hne`, where the
nonzeroness now comes from `CharZero A` (automatic instance for a ℚ-algebra) rather
than the concrete `ℚ_[p]`. `oneAddX_mul_derivative_log` is **already** stated and
proved for general `[CommRing A] [Algebra ℚ A]` (`PadicExp.lean:470`), so the only
helper is already in the right generality.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The ℚ-algebra hypothesis is already a typeclass; no bundled hypothesis to convert. |
| 2 | sequences/metric → filters/topological? | no | — | Pure algebraic identity in `R⟦X⟧`; no convergence/topology in the statement. |
| 3 | construction → universal-property class? | partial → **align with `logOf`** | State as `(exp A).subst (log A) = 1 + X`, i.e. `expOf? (log A) = 1 + X`; mathlib has `logOf f := (log A).subst (f − 1)` with `logOf (1+X) = log A`. The natural mathlib-idiomatic packaging is as the **inverse** to `logOf` (or a forthcoming `expOf`). | Pairs with mathlib's existing `logOf` API (`Log.lean:82–97`) to give the round-trip `expOf (logOf f) = f` style results; the bare `subst` identity is the load-bearing lemma underneath. |
| 4 | set-with-closure-predicate → bundled type? | no | — | n/a. |
| 5 | vector-space/field-specific → weaken typeclass? | **yes (this is the move)** | `[CommRing A] [Algebra ℚ A]` instead of `ℚ_[p]` | This IS the Phase-4b weakening; restated here because it is also the modern-idiom point: mathlib's whole `exp`/`log` API lives over `[CommRing A] [Algebra ℚ A]`, so the inverse identity must too. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure? | no (covered by #5) | — | The only concrete object is the base ring, handled by #5. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it coincides with the Phase-4b literature
weakening (generalise the base ring to `[CommRing A] [Algebra ℚ A]`), with the
secondary observation that the result should live next to / pair with mathlib's
existing `logOf` API.
  - Proposed mathlib-idiomatic restatement: `theorem PowerSeries.exp_subst_log (A : Type*) [CommRing A] [Algebra ℚ A] : (exp A).subst (log A) = 1 + X`
  - Cost: CHEAP.
  - Mathlib downstream this enables: the inverse-pair theorems for `PowerSeries.exp`/`PowerSeries.log` (currently mathlib has the building blocks — `exp`, `log`, `logOf`, `exp_unique_of_derivative_eq_self`, `derivative.ext` — but **no inverse-relationship theorem**); it directly discharges the motivating example named in `Mathlib/RingTheory/PowerSeries/Derivative.lean:22`.
  - Real mathematical improvement: the general statement is reusable by every ℚ-algebra development (formal groups, Bernoulli/exponential-generating-function machinery, the FltRegularBernoulli Dwork work — see Phase 6), whereas the `ℚ_[p]` form is reusable by nothing outside p-adic analysis.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no definitional equality or typeclass-search path introduced).

---

### Mathlib search-status: `PadicLFunctions.exp_subst_log`

[A] Lean-Finder       — natural-language "formal power series exp log inverse"   n/a: Lean-Finder MCP not configured in this environment.
[B] Loogle            `(PowerSeries.exp _).subst (PowerSeries.log _) = _`; `_ = 1 + PowerSeries.X`   n/a: Loogle MCP not configured here. Substituted by exhaustive grep [D] over the full mathlib source tree (`.lake/packages/mathlib/Mathlib/`).
[C] LeanSearch        — "exp of log of one plus X equals one plus X power series"   n/a: LeanSearch MCP not configured here. Covered by [D]+[E].
[D] Grep mathlib src  `exp.*\.subst.*log`, `log.*\.subst.*exp`, `= 1 \+ .*exp`, `log.*subst.*= X`, `expOf`   **no hits** for the formal identity. The only structural matches (`exp … = 1 + …`) are in `Analysis/Normed/Algebra/{Spectrum,TrivSqZeroExt,DualNumber}` — the *analytic* Banach-algebra exponential, unrelated. **No `expOf` exists** (mathlib has only `logOf`).
[E] Name pattern      grep `theorem (exp_log|log_exp|exp_subst|log_subst|expOf)` over mathlib   hits are all `Complex.exp_log`/`Real.exp_log`/`Real.log_exp` (Analysis/SpecialFunctions) — the **analytic** exp/log on ℂ and ℝ, NOT the formal power series. No formal-power-series inverse identity exists.

Searched for both:
  - the user's current form (`(exp ℚ_[p]).subst (log ℚ_[p]) = 1 + X`) — not in mathlib;
  - the literature-standard form (`(exp A).subst (log A) = 1 + X` for general `[CommRing A] [Algebra ℚ A]`) — **also not in mathlib** (this is the key: the general form is missing too, so it is not a NO-mathlib-has-it).

Concluded: **not in mathlib** (grep [D] + name-pattern [E] exhausted, under both the
ℚ_[p] form and the general ℚ-algebra form). Strikingly, mathlib's own
`Mathlib/RingTheory/PowerSeries/Derivative.lean:22` module docstring **names this exact
identity** — "one can easily prove the power series identity `exp(log(1+X)) = 1+X` by
differentiating twice" — as the *motivating example* for the `derivative.ext` tool, but
never adds it as a theorem. That is a textbook named-gap signal.

---

### Call sites — `PadicLFunctions.exp_subst_log`

Internal use count: **K = 1** (within the same project, excluding the declaring file's own statement) — `PadicExp.lean:945`, inside `padicExp_padicLog` (the analytic statement `log(exp x) = x` on the p-adic ball), via the master-bridge that transports the formal identity to the convergent power series.
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PadicExp.lean:945` | `... exp_subst_log, eval_oneAddX]` (rewrite, inside `padicExp_padicLog`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `exp_subst_log`?):
  - **YES — across a different AINTLIB project.** `projects/FltRegularBernoulli/.../DworkFactorization/FiniteLogFormal.lean:31` proves `(d⁄dX A (PowerSeries.log A)) * (1 + PowerSeries.X) = 1` for general `[CommRing A] [Algebra ℚ A]` — i.e. it independently re-derives the **same helper** (`oneAddX_mul_derivative_log`) that underlies `exp_subst_log`, plus `subst_deriv_log_mul_one_add` (its `subst` version). Several other FltRegularBernoulli files (`PadicLogSetup.lean:170`, `DworkParameter/Part1.lean:314`) manipulate `(1 + PowerSeries.X)`/`G * (1 + X) = 1` by hand. This is concrete, repo-wide evidence that the general formal exp/log inversion API is being **duplicated** because mathlib lacks it.

**Composability signal:** K = 1 internal use *alone* would lean toward "possibly the
wrong abstraction / inline it". But the inline-derivation grep flips the reading: the
underlying general identity is re-invented in a *separate* project, so the right fix is
not "inline locally" — it is "ship the general form to mathlib so both projects (and
future ℚ-algebra developments) import it." This is the YES-but-generalise signal.

---

### Composition check (Phase 6)

Can `exp_subst_log` be derived from mathlib in ≤3 chained calls?

Attempt 1: `derivative.ext (by simp [derivative_subst, …]) (by simp [constantCoeff_subst, …])`
  - Mathlib decls used: `PowerSeries.derivative.ext`, `PowerSeries.derivative_subst`, `PowerSeries.derivative_exp`, `PowerSeries.constantCoeff_subst`.
  - Result: **fails as a ≤3-call composition.** `derivative.ext` reduces the goal to (a) equal derivatives and (b) equal constant coefficients, but establishing (a) — `D(exp.subst log) = D(1+X) = 1` — itself requires the chain `derivative_subst` → `derivative_exp` → the geometric-series identity `(1+X)·D(log) = 1` (the project's `oneAddX_mul_derivative_log`, NOT in mathlib), then a `mul`/`mul_comm` manipulation. That is a multi-step proof with non-trivial reasoning between `have`s, not a 1–3 call composition.
  - Notes: the missing link `(1+X)·D(log) = 1` is itself not in mathlib (it is the project helper, also re-derived in FltRegularBernoulli) — so even the "building block" needs adding.

Attempt 2: substitution-inverse machinery (`PowerSeries.substInv` / `subst_substInv_left`)
  - Mathlib decls used: `PowerSeries.substInv`, `subst_substInv_right/left`.
  - Result: **fails.** `substInv` gives *a* composition inverse of an arbitrary series with unit linear coefficient, characterised abstractly (`substInvFun`); it does not identify that inverse as `log` for `exp` or vice versa. Connecting `exp.substInv = log(1+·)` is itself the theorem we want, not a composition of it.

Conclusion: **NOT-COMPOSABLE.** The result needs a genuine proof (the differentiate-twice
argument), and even its key lemma `(1+X)·D(log)=1` is absent from mathlib.

---

## Verdict: `PadicLFunctions.exp_subst_log`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): unanimous — `exp(log(1+X)) = 1+X` is *the* standard formal exp/log mutual-inverse identity, stated over **any commutative ring containing ℚ** (MathOverflow channel #9; char-0 framing channels #2/#3; canonical arXiv "An invitation to formal power series"). The base ring is the only generality dimension, and the literature is more general than the Lean form.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — base ring fixed to `ℚ_[p]` where the literature (and the proof) work over `[CommRing A] [Algebra ℚ A]`. Cost CHEAP. Phase 4c agrees and adds the `logOf`-pairing observation.
- Mathlib search (Phase 5): **not in mathlib**, under either the ℚ_[p] form or the general form. Mathlib's `Derivative.lean:22` docstring names the identity as a motivating example but never proves it; no `expOf` companion to `logOf` exists.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a real differentiate-twice proof; its key lemma `(1+X)·D(log)=1` is itself missing from mathlib.

**Rationale (1–2 paragraphs):**

This is a genuinely missing, genuinely fundamental result — but in the wrong
generality. The identity `exp(log(1+X)) = 1+X` is the formal-power-series statement
that exp and log(1+·) are mutual inverses; the literature is unanimous that it holds
over any ℚ-algebra and is the keystone of, e.g., the binomial series `(1+X)^λ =
exp(λ log(1+X))` and formal-group theory. Mathlib has built out the whole supporting
cast — `PowerSeries.exp`, `PowerSeries.log`, `logOf`, `derivative_exp`,
`exp_unique_of_derivative_eq_self`, and the `derivative.ext` uniqueness tool — and
its `Derivative.lean` header *explicitly advertises* this very identity as the
motivating example for that tool, yet the theorem itself is absent. The proof is not
composable in ≤3 calls (it is the differentiate-twice argument, and even its key
lemma `(1+X)·D(log)=1` is missing from mathlib), so a real lemma is warranted.

The reason this is *generalise-first* and not *add-as-is*: the project states the
identity over `ℚ_[p]`, but the proof uses no p-adic structure whatsoever (verified —
the only `norm` token is the `norm_num` tactic; no norm, ultrametric, completeness, or
summability appears). Every lemma it invokes is mathlib's general `[CommRing A]`
substitution/derivative API plus the project's own `oneAddX_mul_derivative_log`, which
is *already* stated for general `[CommRing A] [Algebra ℚ A]`. The coefficient-recursion
divisions need only `CharZero A`, which mathlib supplies automatically for any
ℚ-algebra (`algebraRat.charZero`). So the generalisation is a mechanical `ℚ_[p] ↦ A`
rewrite. That the general form is the right target is reinforced by Phase 6's
inline-derivation finding: a *separate* AINTLIB project, `FltRegularBernoulli`, has
independently re-derived the same general helper (`FiniteLogFormal.lean`) — duplication
that only a mathlib-level general statement removes.

**Reason for the generalisation:** LITERATURE-WEAKENING (Phase 4b found the `ℚ_[p]`
form strictly narrower than the literature-standard `[CommRing A] [Algebra ℚ A]` form;
Phase 4c concurs and notes the mathlib-idiomatic packaging next to `logOf`).

**Proposed restatement:**

```lean
namespace PowerSeries

/-- The formal exponential and logarithm are mutually inverse:
`exp(log(1 + X)) = 1 + X` over any `ℚ`-algebra. -/
theorem exp_subst_log (A : Type*) [CommRing A] [Algebra ℚ A] :
    (exp A).subst (log A) = 1 + X := by
  sorry  -- the existing PadicExp.lean proof with `ℚ_[p]` replaced by `A`;
         -- `oneAddX_mul_derivative_log` is already general; nat-cast nonzeroness
         -- comes from the automatic `CharZero A` instance for ℚ-algebras.

end PowerSeries
```

**Estimated cost of regeneralisation:** **CHEAP** (mechanical rewrite). EXPENSIVE
would not downgrade the verdict regardless — but here it is genuinely cheap.

**Mathlib downstream this enables (REQUIRED):**
- Discharges the motivating identity explicitly named in `Mathlib/RingTheory/PowerSeries/Derivative.lean:22`.
- Supplies the **inverse-relationship theorem** for the existing `PowerSeries.exp`/`PowerSeries.log` API (mathlib currently has the pieces — `exp`, `log`, `logOf`, `exp_unique_of_derivative_eq_self`, `derivative.ext` — but no statement that they invert).
- Pairs with `PowerSeries.logOf` (`Log.lean:82`); together with the companion direction (see PR grouping) it gives the round-trip needed for `(1+X)^s`-style binomial / formal-group developments.
- Removes the cross-project duplication of the `(1+X)·D(log)=1` helper now re-derived in `FltRegularBernoulli` (`FiniteLogFormal.lean`).

**PR grouping (required):** Ship as **one PR** with the file's companion theorem
`PadicLFunctions.log_subst_exp_sub_one` (`PadicExp.lean:540`), which proves the other
inverse direction `log(1 + (exp − 1)) = X` and is *also* over-specialised to `ℚ_[p]`
with a purely-algebraic proof. The two together are the "exp and log are mutually
inverse formal power series" pair. The helper `PadicLFunctions.oneAddX_mul_derivative_log`
(`PadicExp.lean:470`, already general) should ship in the same PR as the supporting
lemma (likely as `PowerSeries.oneAddX_mul_deriv_log` or folded into `Log.lean`).

**Proposed mathlib location:** `Mathlib/RingTheory/PowerSeries/Log.lean` (the natural
home — it already imports `Exp` and `Substitution` and defines `logOf`).

**Pre-PR checklist before opening:**
- [ ] Run `/generalise PadicLFunctions.exp_subst_log` to confirm `[CommRing A] [Algebra ℚ A]` is the right typeclass cluster (and that `IsAddTorsionFree`/`CharZero` need not be carried explicitly — it should be inferred).
- [ ] `/cleanup` the generalised `exp_subst_log` + `log_subst_exp_sub_one` + helper as a batch.
- [ ] Confirm naming with mathlib convention (`exp_subst_log` vs `exp_comp_log`/`exp_logOf`); align with the `logOf` naming already in `Log.lean`.
- [ ] Pick a reviewer from recent `Mathlib/RingTheory/PowerSeries/` commits (the `Exp`/`Log`/`Derivative` files are by Yuma Mizuno, Ralf Stephan, Richard M. Hill).

**Next action:** run `/generalise PadicLFunctions.exp_subst_log` (it will tension
against the literature-standard `[CommRing A] [Algebra ℚ A]` form from Phase 3 and the
`logOf`-aligned modern-idiom form from Phase 4c), restate over a general ℚ-algebra,
batch with `log_subst_exp_sub_one` + `oneAddX_mul_derivative_log`, then open the mathlib
PR against `Mathlib/RingTheory/PowerSeries/Log.lean`.

---

## Next step

Run `/generalise PadicLFunctions.exp_subst_log` to restate over `[CommRing A] [Algebra ℚ A]`,
batch with the companion `log_subst_exp_sub_one` and the helper `oneAddX_mul_derivative_log`
(both also general and purely algebraic), then open a single `feat(RingTheory/PowerSeries)`
PR adding the formal exp/log mutual-inverse identities to `Mathlib/RingTheory/PowerSeries/Log.lean`.
