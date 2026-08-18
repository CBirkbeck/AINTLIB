# `PadicLFunctions.coe_norm_le_inv_of_mem_span` — mathlibable assessment

**Verdict: `NO-composable-from-mathlib`**

`coe_norm_le_inv_of_mem_span` states that an element `x ∈ ℤ_[p]` lying in the
ideal `span {p}` has `ℚ_[p]`-norm `‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹`. This is the
single most elementary fact of `p`-adic analysis — "the maximal ideal `pℤ_p` is
exactly `{x : |x|_p < 1}`, with the sharp bound `|x|_p ≤ 1/p`" — stated in every
introductory text (Koblitz, Cassels, K. Conrad's notes, …). In mathlib it is the
`n = 1` specialisation of `PadicInt.norm_le_pow_iff_mem_span_pow`, bridged from the
`ℤ_[p]`-norm to the `ℚ_[p]`-norm by `PadicInt.norm_def` (which is `rfl`). The
project's own proof is a **2-named-mathlib-lemma composition** (`norm_def` +
`norm_le_pow_iff_mem_span_pow`) with only pure power/cast normalisation as glue
(`zpow_neg`, `zpow_one`, `pow_one`) — inside the ≤3-call budget. No new lemma is
justified for mathlib.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1000` (kind: `theorem`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

---

## Phase 0 — Doctor / baseline

Per the task's BUILD NOTE, the build was **not re-run; reasoned from source.**
The declaration, its proof, its dependents, and the relevant mathlib API were read
directly from `PadicExp.lean` and from the mathlib package under
`.lake/packages/mathlib/Mathlib/NumberTheory/Padics/`. Baseline commit `e28d694`
(branch `main`). No `sorry` in the target or in any of its in-file consumers
(`grep sorry/admit` over `PadicExp.lean`: none). This is the Phase-0
source-fallback path the skill permits.

---

## Phase 1 — Comprehend

```lean
omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: an element of `pℤ_p` has `ℚ_[p]`-norm at most `p⁻¹` (the coe-norm of
`PadicInt.norm_le_pow_iff_mem_span_pow` at exponent `1`; RJW Lem 5.14). -/
theorem coe_norm_le_inv_of_mem_span {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [← PadicInt.norm_def, show ((p : ℝ)⁻¹) = (p : ℝ) ^ (-((1 : ℕ) : ℤ)) by
    rw [zpow_neg, Nat.cast_one, zpow_one]]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x 1).2 (by simpa using hx)
```

**Mathematical content.** `ℤ_[p]` is a complete DVR (local PID) with maximal
ideal `𝔪 = pℤ_p = Ideal.span {(p : ℤ_[p])}`. Its norm is `‖x‖ = p^{-v_p(x)}`,
where `v_p` is the (normalised) `p`-adic valuation. Membership `x ∈ span {p}`
means `p ∣ x`, i.e. `v_p(x) ≥ 1`, hence `‖x‖ = p^{-v_p(x)} ≤ p^{-1} = 1/p`. The
theorem records this with the norm taken in `ℚ_[p]` (via the coercion
`ℤ_[p] ↪ ℚ_[p]`), which is the form needed by the surrounding `p`-adic
exponential development.

**Type-class context.** File-level `variable (p : ℕ) [hp : Fact p.Prime]` and
`{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]
[CompleteSpace L]`. The `omit` line strips `NormedAlgebra ℚ_[p] L`,
`IsUltrametricDist L`, `CompleteSpace L` — i.e. the statement depends **only** on
`[Fact p.Prime]` and the fixed concrete types `ℤ_[p]`, `ℚ_[p]`. `L` is irrelevant
to it; the result is purely about `PadicInt`/`Padic` for a single prime `p`.

**Proof reading (what each step does).**
1. `rw [← PadicInt.norm_def]`: `PadicInt.norm_def : ‖z‖ = ‖(z : ℚ_[p])‖` is `rfl`;
   rewriting backwards turns the goal `‖(x : ℚ_[p])‖ ≤ (p:ℝ)⁻¹` into the
   `ℤ_[p]`-norm goal `‖x‖ ≤ (p:ℝ)⁻¹`.
2. `rw [show (p:ℝ)⁻¹ = (p:ℝ)^(-(1:ℕ:ℤ)) …]`: pure arithmetic normalisation
   (`zpow_neg`, `Nat.cast_one`, `zpow_one`) rewriting `(p:ℝ)⁻¹` as `(p:ℝ)^(-1:ℤ)`
   to match the RHS shape of the mathlib iff.
3. `exact (PadicInt.norm_le_pow_iff_mem_span_pow x 1).2 (by simpa using hx)`:
   the `.2` direction of `norm_le_pow_iff_mem_span_pow x 1`
   (`‖x‖ ≤ p^{-1} ↔ x ∈ span {p^1}`), fed `x ∈ span {p^1}` which `simpa`
   (`pow_one`) obtains from `hx : x ∈ span {p}`.

**Role in the development.** It is the foundational norm bound for the `pℤ_p`
branch of RJW Lemma 5.14: it feeds `inExpBall_of_mem_span` (line 1017 —
`pℤ_p ⊂` exp convergence ball for odd `p`), `pZpExp_coe` (line 1053), and three
further `pℤ_p`-integral results (lines 1069, 1090, 1104, 1136). All consumers are
**inside this one file** (see Phase 6.0).

---

## Phase 2 — Preliminary BIG/SMALL + one-line check

**SMALL.** A single `≤` between two reals, derived in three short proof steps from
one mathlib iff plus a defeq norm bridge and pure power normalisation.

**One-line check.** The result does **not** follow from a single mathlib `exact`,
but it *does* follow from a short composition. Concretely, the conclusion
`‖(x : ℚ_[p])‖ ≤ (p:ℝ)⁻¹` is defeq (via `norm_def`, `rfl`) to `‖x‖ ≤ (p:ℝ)⁻¹`, and
mathlib's `norm_le_pow_iff_mem_span_pow x 1` is `‖x‖ ≤ (p:ℝ)^(-1:ℤ) ↔ x ∈ span{p^1}`.
The two sides differ only by the *purely syntactic* normalisations
`(p:ℝ)⁻¹ = (p:ℝ)^(-1:ℤ)` and `span{p} = span{p^1}`. So this is right on the
`NO-mathlib-has-it` ↔ `NO-composable-from-mathlib` boundary; the deciding question
is whether a *single named call* closes it (→ `NO-mathlib-has-it`) or whether a
short *composition* is needed (→ `NO-composable`). Phases 5–6 resolve this: a short
composition is needed (norm bridge + iff direction + two normalisation rewrites),
so it is `NO-composable-from-mathlib`, not `NO-mathlib-has-it`.

**Exemptions considered (defeq-abuse / diamond / API-stability):** N/A — this is a
`theorem`, not a `def`/`class`/`instance`, so there is no diamond/defeq-abuse
concern and no instance-API-stability surface to preserve.

---

## Phase 3 — Exhaustive literature search (9 channels)

Goal: pin the **literature-standard form** of "an element of the maximal ideal
`pℤ_p` has norm `≤ 1/p`", and confirm whether it is a *named result* or a
definition-level triviality.

| # | Channel | Query | Finding |
|---|---------|-------|---------|
| 1 | WebSearch | "p-adic integer multiple of p has absolute value at most 1/p valuation" | Unanimous: `|x|_p = p^{-v_p(x)}`; a multiple of `p` has `v_p ≥ 1`, so `|x|_p ≤ p^{-1} = 1/p`. The unit ball `{|·|≤1}` is `ℤ_p`. Textbook-level. |
| 2 | WebSearch | "p-adic valuation maximal ideal pZ_p norm bound Koblitz Cassels" | `pℤ_p = {x ∈ ℚ_p : |x| < 1}` is **the** maximal ideal of `ℤ_p`, a local ring with maximal ideal `(p)`. Cites Koblitz's text and Cassels as the standard references — exactly the file's docstring references (RJW cites Cassels §12). |
| 3 | WebSearch | `"p-adic" element divisible by p norm "1/p" ultrametric ring of integers` | `ℤ_p = {x : |x|_p ≤ 1}`; `|x|_p = p^{-k}` for `x = p^k·(unit)`; "elements with more factors of `p` have smaller norm". The bound `|x|_p ≤ 1/p ⟺ p ∣ x` is stated as immediate. |
| 4 | **K. Conrad notes** (kconrad.math.uconn.edu, "p-adic analysis/arithmetic", via #1/#3) | norm vs divisibility | Standard lecture treatment: `‖x‖_p ≤ 1/p ⟺ p ∣ x` in `ℤ_p`; the maximal ideal is `pℤ_p = {‖·‖<1}`. Definition-level. |
| 5 | **Leiden / Evertse Ch. 8** (pub.math.leidenuniv.nl/~evertsejh/dio15-8.pdf, via #2) | structure of `ℤ_p` | `ℤ_p` is a local PID, `pℤ_p = {x : |x|_p < 1}` maximal; `|x|_p ∈ {p^{-k}}`. Confirms the sharp `≤ 1/p` bound on `pℤ_p`. |
| 6 | **arXiv** (via #2: "A formal proof of Hensel's lemma over the p-adic integers", 1909.11342; "Formalizing the Ring of Witt Vectors", 2010.02595) | norm/valuation API in formalised `p`-adics | These formalisation papers use exactly the mathlib `PadicInt` norm/valuation API where `‖x‖ ≤ p^{-n} ⟺ x ∈ span{p^n}`; our statement is the `n=1` coe-form of that. |
| 7 | **Wikipedia** ("p-adic valuation", via #1) | definition `|x|_p = p^{-v_p(x)}` | `|x|_p = p^{-ν_p(x)}`; multiplying by `p` divides the absolute value by `p`. The `≤ 1/p` bound on multiples of `p` is the immediate consequence. |
| 8 | **Encyclopedia of Mathematics** ("P-adic valuation", encyclopediaofmath.org, via #1/#2) | normalised valuation | Same normalisation; `ℤ_p`, `pℤ_p` structure as above. No "named theorem"; it is part of the definition of the `p`-adic absolute value. |
| 9 | **ChatGPT MCP** (historical-formulation question) | not available in this environment | **Channel unavailable** (no ChatGPT MCP configured). Compensated by channels 1–8, which converge unanimously and decisively; recorded for completeness per the skill's gate. |

**Literature-standard form (synthesised).** "An element of `pℤ_p` has `p`-adic
absolute value `≤ 1/p`" (equivalently `pℤ_p = {x : |x|_p < 1}`, the maximal ideal)
is a **definition-level fact** of `p`-adic analysis: it is the immediate
consequence of `|x|_p = p^{-v_p(x)}` together with `p ∣ x ⟺ v_p(x) ≥ 1`. It is
*everywhere* (Koblitz, Cassels, Conrad, Leiden, Wikipedia, EoM) and is **never a
named theorem** — it is part of how the `p`-adic absolute value and the local ring
`ℤ_p` are *defined*. There is no research-level "general form" to target; the only
question is what mathlib already has (Phases 5–6).

---

## Phase 4 — Generality vs literature-standard

**Already at the standard level; no literature-supported generalisation axis that
keeps it a single statement.** Observations:

- **Type-class footprint is minimal.** Via `omit`, the statement needs only
  `[Fact p.Prime]`; `L` and its three classes are irrelevant. It is stated on the
  concrete `ℤ_[p]`/`ℚ_[p]`, which *is* the natural home of the fact.
- **The natural mathlib generalisation already exists and is more general:**
  `PadicInt.norm_le_pow_iff_mem_span_pow x n` covers **all** exponents `n` (the
  whole filtration `‖x‖ ≤ p^{-n} ⟺ x ∈ span{p^n}`), not just `n = 1`, and as an
  `Iff` (both directions), not just the `←` bound. Our target is the **strictly
  narrower** `n = 1`, single-direction, coe-to-`ℚ_[p]` specialisation. So the
  "more general form" is not a new contribution — **mathlib already has it**
  (this is what makes the verdict `NO-…`, see Phase 5).
- **Abstract-DVR generalisation** ("element of the maximal ideal of a DVR with a
  rank-1 valuation has norm `≤ (uniformiser-norm)`") is a real generalisation axis,
  but (i) it is no longer the *same statement* and (ii) the corresponding mathlib
  API (`IsDiscreteValuationRing`, `Valued`, `WithVal`) handles it through valuation
  inequalities, not a bespoke lemma; pursuing it would be a different declaration
  about a different object, not a restatement of this one. Not a YES-generalise
  target for *this* lemma.

No restatement keeps this exact result while strictly widening it; the strictly
wider thing (`norm_le_pow_iff_mem_span_pow`) is already in mathlib.

---

## Phase 4c — Modern-mathlib-idiom restatement (the Bourbaki 2.0 check)

**Does a contemporary mathlib idiom re-state this with real downstream
consequences?** No, and mathlib already demonstrates the idiom:

- The modern mathlib framing of "norm bounded by a power of `p` ⟺ membership in a
  power of the maximal ideal" is precisely **`PadicInt.norm_le_pow_iff_mem_span_pow`**
  — an `Iff` between an analytic bound and an *ideal-membership* (algebraic) side,
  i.e. exactly the norm-vs-`span` bridge that `coe_norm_le_inv_of_mem_span` invokes.
  Mathlib also offers the valuation-side idiom `norm_le_pow_iff_le_valuation`
  (line 449) and the DVR/`Valued` machinery (`maximalIdeal_eq_span_p`,
  `IsDiscreteValuationRing ℤ_[p]`). The idiomatic tools are **already present**.
- The one *encoding* wrinkle in the target — taking the norm in `ℚ_[p]` via the
  coercion rather than the `ℤ_[p]`-norm — is **not** a modernisation; `norm_def`
  is `rfl`, so the two are definitionally the same and mathlib treats `‖z‖` and
  `‖(z : ℚ_[p])‖` interchangeably (`padic_norm_e_of_padicInt`,
  `norm_intCast_eq_padic_norm`). Choosing the `ℚ_[p]` side is a local convenience,
  not a structural improvement.
- Per the verdicts reference's rule 5 ("modernisation must be a real improvement in
  mathematical organisation; 'it looks cooler' is not enough"), there is **no**
  downstream API that `coe_norm_le_inv_of_mem_span` unlocks that
  `norm_le_pow_iff_mem_span_pow` (+ `norm_def`) does not already provide. It is the
  *narrowing* of an existing idiomatic lemma, not a new idiom.

This is the opposite of a Bourbaki-2.0 win: the general, idiomatic statement
already exists; the target is its `n=1` shadow.

---

## Phase 5 — Mathlib five-method search

Searched for (a) the exact statement (coe-norm of a `span{p}` element `≤ p⁻¹`) and
(b) the general norm-vs-`span{p^n}` correspondence.

| Method | Query | Result |
|--------|-------|--------|
| Loogle (web) | `PadicInt.norm_le_pow_iff_mem_span_pow` | **Hit.** Confirms the canonical lemma: `‖x‖ ≤ p^{-n} ↔ x ∈ Ideal.span {p^n}` for `x : ℤ_[p]`, `n : ℕ`. This is the direct general form of the target. |
| grep (decl) | `norm_le_pow_iff_mem_span_pow` in `mathlib/` | `Mathlib/NumberTheory/Padics/PadicIntegers.lean:466`. Used internally (RingHoms.lean, ProperSpace.lean, CyclotomicCharacter.lean, DividedPowers/Padic.lean) — a load-bearing mathlib lemma. |
| grep (norm bridge) | `theorem norm_def` in `Padics/` | `PadicIntegers.lean:191`: `‖z‖ = ‖(z : ℚ_[p])‖ := rfl`. Also `padic_norm_e_of_padicInt` (226), `norm_intCast_eq_padic_norm` (228) — the `ℤ_[p]`↔`ℚ_[p]` norm bridge is fully present and defeq. |
| grep (exact target) | `‖(.*: ℚ_[p])‖ ≤ (p : ℝ)⁻¹`, `span {(p : ℤ_[p])}` ⇒ norm bound, `mem_maximalIdeal` ⇒ `≤ p⁻¹` in `Padics/` | **No** lemma states the `n=1` coe-norm bound `‖(x:ℚ_[p])‖ ≤ p⁻¹` for `x ∈ span{p}` as its own declaration. Mathlib derives such things on the fly (e.g. `norm_lt_one_iff_dvd` at 482 specialises `norm_le_pow_iff_mem_span_pow x 1` for the *strict* `<1` form). |
| LeanSearch / grep (auxiliary) | `norm_p` (= `(p:ℝ)⁻¹`, lines 234/854), `norm_lt_one_iff_dvd`, `maximalIdeal_eq_span_p` (506), `norm_le_pow_iff_le_valuation` (449) | Building blocks all present. The closest sibling, `norm_lt_one_iff_dvd : ‖x‖ < 1 ↔ p ∣ x`, is the `<1` analogue and is itself proved from `norm_le_pow_iff_mem_span_pow x 1` — confirming the target's fact is a one-step consequence of that lemma, not an independent result. |

**Conclusion of Phase 5.** Mathlib has the **strictly more general** result
`PadicInt.norm_le_pow_iff_mem_span_pow` (all `n`, both directions) plus the
`norm_def` bridge, but does **not** carry the `n=1` coe-`ℚ_[p]` `≤ p⁻¹` form as a
named lemma. So this is not a literal `NO-mathlib-has-it` (no single named decl is
our exact statement), but mathlib *does* have everything needed — pushing the
decision to the composition check (Phase 6). [If one insists on the
`NO-mathlib-has-it` reading because the general lemma subsumes ours, the
one-liner is shown below; either way the answer is "do not add to mathlib".]

---

## Phase 6 — Composition check (≤3 mathlib calls?)

### Phase 6.0 — Call-sites table (required artifact)

| Location | Uses of `coe_norm_le_inv_of_mem_span` | Nature |
|----------|--------------------------------------|--------|
| `PadicExp.lean` (own file) | **6** call sites: lines 1017, 1053, 1069, 1090, 1104, 1136 | Foundational norm bound for the `pℤ_p`-branch of RJW Lem 5.14 (`inExpBall_of_mem_span`, `pZpExp_coe`, and 3 further integral-branch results). All `exact …` / `(…).trans …`. |
| Rest of `projects/` (all other `.lean`) | **0** | Grep over `projects/` minus `PadicExp.lean`: no matches. |
| Mathlib | 0 | N/A. |

**K = 6 in-file uses, 0 external.** It is a genuine internal helper for *this*
file's `pℤ_p` development, with no cross-project consumers. By the call-sites
heuristic this is a real local API node, but a thin one: each consumer wants only
the `≤ p⁻¹` bound, obtained from a 2-lemma mathlib composition.

### Composition (the proof IS the composition)

The target is exactly a short composition of existing mathlib decls:

```lean
example {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [← PadicInt.norm_def, show (p : ℝ)⁻¹ = (p : ℝ) ^ (-(1 : ℤ)) by simp]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x 1).2 (by simpa using hx)
```

**Substantive mathlib calls counted:**
1. `PadicInt.norm_def` (the `ℚ_[p]`↔`ℤ_[p]` norm bridge, `rfl`).
2. `PadicInt.norm_le_pow_iff_mem_span_pow` (the general norm-vs-`span` iff),
   `.2` direction.

Everything else is **pure normalisation glue**, not mathematical content:
`zpow_neg`/`zpow_one`/`Nat.cast_one` (or a one-shot `simp`) to rewrite
`(p:ℝ)⁻¹ = (p:ℝ)^(-1:ℤ)`, and `pow_one` (inside `simpa`) to turn `span{p}` into
`span{p^1}`. That is **2 named lemma calls + arithmetic normalisation**, well
inside the ≤3-call budget, and it is a real composition (an `exact` of an iff
direction fed a normalised hypothesis), **not** a proof in disguise (no
`linarith`/`nlinarith`/multi-step reasoning, no case analysis — only defeq and
`simp`-level rewriting of power/cast forms).

**COMPOSABLE.** A 1–3 line composition of `PadicInt.norm_def` and
`PadicInt.norm_le_pow_iff_mem_span_pow` (with `simp`-level normalisation) gives the
result at every call site; no standalone mathlib lemma is justified.

---

## Phase 7 — Synthesis and verdict

- Phase 2: SMALL; on the `NO-mathlib-has-it` ↔ `NO-composable` boundary; resolved
  by Phases 5–6 to composable (norm bridge + iff direction needed, not a single
  `exact`).
- Phase 3 (9 channels): the fact "`x ∈ pℤ_p ⇒ |x|_p ≤ 1/p`" is a **definition-level
  triviality** of `p`-adic analysis (Koblitz, Cassels, Conrad, Leiden, Wikipedia,
  EoM), **never a named theorem**. No research-level general form to target.
- Phase 4 / 4c: the natural, idiomatic, **strictly more general** mathlib statement
  already exists (`PadicInt.norm_le_pow_iff_mem_span_pow`, all `n`, both
  directions); the target is its `n=1`, single-direction, coe-`ℚ_[p]`
  specialisation. No modernisation contribution; the coe-`ℚ_[p]` framing is a
  `rfl`-level convenience, not a structural improvement.
- Phase 5: mathlib has the general iff + the `norm_def` bridge + all building
  blocks (`norm_p`, `maximalIdeal_eq_span_p`, `norm_lt_one_iff_dvd`); it does not
  carry this exact `n=1` coe-form as a named decl.
- Phase 6: **K = 6 in-file / 0 external** consumers; the body is a genuine 2-call
  composition (`norm_def` + `norm_le_pow_iff_mem_span_pow`) with only
  power/cast-normalisation glue → **COMPOSABLE** within ≤3 calls.

These converge on **`NO-composable-from-mathlib`** (matching Case 4 of the verdicts
reference: a small wrapper whose body is a ≤3-call composition of existing mathlib
facts). Cost is not a factor here in either direction — the composition is genuinely
short, so there is no expensive generalisation being declined.

**Boundary note (`NO-mathlib-has-it` vs `NO-composable`).** Because mathlib's
`norm_le_pow_iff_mem_span_pow` strictly subsumes the statement, one could also file
this as `NO-mathlib-has-it` "modulo the `norm_def` defeq and a `simp` of power/cast
forms". Either reading yields the same actionable conclusion: **do not contribute
this to mathlib.** It is recorded as `NO-composable-from-mathlib` because the exact
`ℚ_[p]`-coe statement is reached by a (tiny) composition rather than a single named
`exact`, which is the more precise description of the proof obligation.

**Project-local recommendation.** Keep `coe_norm_le_inv_of_mem_span` as a
project-local helper — its 6 in-file uses make it useful sugar for the `pℤ_p`
branch — but do not PR it. If the surrounding `p`-adic exp/log API is ever
upstreamed, its consumers should call `PadicInt.norm_le_pow_iff_mem_span_pow`
(with `norm_def` + a `simp` normalisation) directly, rather than carrying a bespoke
`n=1` coe-lemma into mathlib. The substantive, genuinely contributable mathematics
of this file lives in the `padicExp`/`padicLog` API and RJW Lem 5.14, assessed
under those declarations — not in this elementary norm bound.

### Final verdict (five-bucket)

> ## **`NO-composable-from-mathlib`**

**Next action:** keep `coe_norm_le_inv_of_mem_span` project-local; do **not** PR it.
At any future upstreaming, replace it with a direct
`(PadicInt.norm_le_pow_iff_mem_span_pow x 1).2`-style call composed with
`PadicInt.norm_def` and `simp`-level power/cast normalisation. Building blocks:
`PadicInt.norm_def` (`Mathlib/NumberTheory/Padics/PadicIntegers.lean:191`),
`PadicInt.norm_le_pow_iff_mem_span_pow` (`…/PadicIntegers.lean:466`).
