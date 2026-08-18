# `/mathlibable` report — `PadicLFunctions.sum_seriesEval_FtildeA`

**Final verdict: `BORDERLINE-needs-human`.**

Mode A, full 10-phase workflow, exhaustive literature sweep. Build was not
re-run (stale/slow); reasoned from source per the Phase-0 fallback.

---

### Baseline (Phase 0)

- lake build:               not re-run; reasoned from source (Phase-0 fallback)
- decl `PadicLFunctions.sum_seriesEval_FtildeA`: resolved at
  `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:1481`
- kind:                      theorem
- has sorry:                 no (proof complete, lines 1481–1583)
- namespace:                 `PadicLFunctions` (in `section mass`; no inner namespace) →
  qualified name `PadicLFunctions.sum_seriesEval_FtildeA`
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" —
  the file formalises the residue/value-at-one of the p-adic zeta function following
  the Rodrigues Jacinto–Williams notes, working over a field `K ⊇ ℚ_p(μ_p)` (e.g. ℂ_p)
  and descending by injectivity.

---

### Statement (Phase 1)

`PadicLFunctions.sum_seriesEval_FtildeA` is a **theorem** stating the following.

Let `p` be an odd prime, `K` a complete ultrametric normed `ℚ_p`-algebra of
characteristic 0 (the working field contains `μ_p`), `a` a natural number with
`p ∤ a` and `a ≠ 0`, and `ξ ∈ K` a primitive `p`-th root of unity. Then the sum
over the `p`-th roots of unity of the **series evaluation** of RJW's explicit
antiderivative power series `F̃_a` collapses to (minus) the extended p-adic
logarithm of `a`:

$$\sum_{i=0}^{p-1} \widetilde{F}_a(\xi^i - 1) \;=\; -\log_p(a).$$

Here `F̃_a` (project def `FtildeA`) is RJW's
`F̃_a = log(T/(1+T) · (1+T)^a/((1+T)^a − 1))`, realised as
`F̃_a = C(−log_p a) − formalLog ∘ (u_a − 1) + (a−1)·formalLog`; `seriesEval F z = Σ_n (coeff_n F)·zⁿ`
is junk-total power-series evaluation; and `log_p = extLog` is the project's
Iwasawa-branch (`log_p p = 0`) extended logarithm (`ExtLog.lean`).

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; `hp2 : p ≠ 2` forces `p` odd (so `p−1 ≥ 2`).
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
  — the ambient p-adic field; `μ_p ⊆ K` supplied by the `ξ` hypothesis.
- `{a : ℕ}` — the natural-number argument of the antiderivative.
- `{ξ : K}` — a chosen primitive p-th root of unity.

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — oddness (gives `p − 1 ≥ 2`, needed for the exp-ball membership).
- `ha : ¬ (p : ℕ) ∣ a` — `p ∤ a` (so `(a:K)` is a unit; drives the `{ξ^a} = μ_p` reindex).
- `ha0 : a ≠ 0` — non-degeneracy (`u_a` is a genuine unit; constant coeff `1`).
- `hξ : IsPrimitiveRoot ξ p` — `ξ` generates `μ_p`.

Conclusion (math): the `μ_p`-trace of `F̃_a` is `−log_p(a)`.
Conclusion (Lean): `∑ i : Fin p, seriesEval (FtildeA p K a) (ξ ^ (i:ℕ) − 1) = −(extLog p ((a:K)))`.

**Source identification (load-bearing).** This is *not* RJW Lemma 7.5 itself.
RJW Lemma 7.5 reads `((1 − φ∘ψ) F̃_a)(0) = −(1 − p⁻¹)·log_p(a)` and is the project's
*sibling* theorem `constantCoeff_mahlerK_rhoA` (`ResidueZeta.lean:1587`). The target
here is the **internal `φ∘ψ` step inside RJW's proof of Lemma 7.5** — the computation
that `(φ∘ψ)(F̃_a)(0) = (1/p)·Σ_{ξ∈μ_p} F̃_a(…) = −p⁻¹·log_p(a)`. The docstring's
"RJW Lemma 7.5's trace, TeX 2330–2349" names exactly this sub-step. It is below
the granularity the source bothers to number.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (but a substantial, ~100-line glue step).
Reason: it is a proof step inside one lemma's proof in one construction — not a new
structure, not named after a person/place, not a `## Main results` headline (the
headline is `Theorem 7.1`, the residue itself, downstream of this).

(Literature width was EXHAUSTIVE regardless. The SMALL tag only frames the report:
this is internal bookkeeping, which biases away from a standalone mathlib lemma.)

### One-line check (Phase 2b)

Body line count: ~100 substantive lines. One-liner verdict: **n/a — kind is `theorem`.**

---

### PHASE 3 — Literature search (EXHAUSTIVE)

#### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic L-function residue at s=1 sum over p-th roots of unity antiderivative power series equals p-adic logarithm" | partial | residue of ζ_p at s=1 is `1−p⁻¹`; `−log_p(1−x)=Σ xⁿ/n` | confirms the *ambient* result + that p-adic log is a power series; the **specific sum identity is not surfaced as a named result** |
| 2 | WebSearch (general/Iwasawa) | "Iwasawa p-adic L-function Mahler transform measure residue zeta_p logarithm formula sum roots of unity" | partial | ζ_p has a simple pole at s=1; Mahler transform = dual of `C(ℤ_p,ℤ_p)`; Iwasawa's `log_p` of principal units recovered from value at s=1 | the *machinery* is standard; the sum-collapse step is not independently named |
| 3 | WebSearch (named-after / textbook) | Washington "Introduction to Cyclotomic Fields" p-adic L-function log-derivative power series roots-of-unity sum | yes (ambient) | Washington Ch. 7 "Iwasawa's Construction of p-adic L-functions" — group rings + power series | the construction lives here; no isolated `Σ F̃_a(ξⁱ−1)=−log_p a` lemma |
| 4 | WebSearch (verbatim shape) | `"F tilde"` power series eval over p-th roots collapse `"-log_p(a)"` residue mass | no | — | the exact shape returns only generic p-adic-analysis hits; no standalone statement |
| 5 | WebSearch (product→sum) | p-adic log of product over Galois conjugates `Πξ(Xξ−1)=Xᵖ−1`, `Σlog = log norm` | partial | `Π_{ξ∈μ_p}(Xξ−1)=Xᵖ−1` is the standard cyclotomic identity; `log_p` additive on principal units | both ingredients are standard; their *combination here* is the proof step, not a named lemma |
| 6 | **Source identification** (decisive) | "RJW p-adic L-functions … residue zeta_p Theorem 7.1 Lemma 7.5 antiderivative" | **yes** | identifies **RJW = Rodrigues Jacinto + Williams, "An Introduction to p-adic L-functions"** (arXiv 2309.15692 / Essential Number Theory 4 (2025) no. 1) | the project follows this verbatim (§7 = "The residue of ζ_p at s=1") |
| 7 | **Primary source, verbatim** (`pdftotext` of the MSP PDF) | §7 Lemmas 7.1–7.5 + proofs | **yes** | §7 is exactly the project file. Lemma 7.5: `((1−φ∘ψ)F̃_a)(0)=−(1−p⁻¹)log_p(a)`; eq (7-5): `F̃_a=log(T/((1+T)ᵃ−1)·(1+T)ᵃ⁻¹)`; the `φ∘ψ` step uses `Π_{ξ∈μ_p}(Xξ−1)=Xᵖ−1` and `{ξᵃ:ξ∈μ_p}=μ_p` to collapse the μ_p-sum | **the target = the unnumbered `φ∘ψ`-trace inside the proof of Lemma 7.5** |
| 8 | nLab | "Iwasawa theory", p-adic L-function residue / p-adic log | no (for this) | nLab "Iwasawa theory" exists (Kubota–Leopoldt ζ_p, main conjecture) but at survey altitude — no per-step lemma | not a categorical concept; nLab carries no antiderivative-sum identity |
| 9 | nCatLab | (categorical?) | n/a | — | not a categorical concept — an explicit p-adic analytic computation |
| 10 | Stacks Project | (alg-geom?) | n/a | — | not an algebraic-geometry concept |
| 11 | MathOverflow / Math.SE | sum over μ_p of p-adic log = log; Iwasawa ζ_p residue trace | n/a (blocked) | — | `mathoverflow.net` and `math.stackexchange.com` are blocked for the fetch agent; WebSearch could not query them. Recorded as a forced n/a, not a skip. |
| 12 | recent arXiv (≤5 yr) | formalization Lean/mathlib p-adic L-function residue ζ_p / p-adic log power series roots of unity | yes (context) | **arXiv 2302.14491** (Narayanan, "Formalization of p-adic L-functions in Lean 3" — Kubota–Leopoldt via Bernoulli numbers) and **arXiv 2503.00959** ("Formalizing zeta and L-functions in Lean", Riemann/Dirichlet) | establishes the state of the art: the Lean-3 p-adic L-function work exists but is **not** in mathlib4; the residue-at-1 / `extLog` route is not formalised anywhere public |
| 13 | ChatGPT MCP | (standard form + generality + historical evolution) | **n/a — not configured** | — | the ChatGPT MCP server is not installed in this environment (only unrelated auth stubs surfaced). Substituted with extra WebSearch (#4, #5) + a verbatim primary-source extraction (#7), which answers the standard-form/generality question directly from RJW. |

#### Literature summary (Phase 3)

Concept identified as: **the `φ∘ψ`-trace step inside the proof of RJW Lemma 7.5**
(Rodrigues Jacinto–Williams, *An Introduction to p-adic L-functions*, §7 "The
residue of ζ_p at s = 1"). Mathematically: the `μ_p`-trace of the antiderivative
power series `F̃_a` evaluates to `−log_p(a)`, via `Π_{ξ∈μ_p}(Xξ−1)=Xᵖ−1` and the
`{ξᵃ}=μ_p` reindex for `p∤a`.

Sources agree on the standard form: **n/a — there is no standard *standalone* form.**
The literature names the *ambient* result (Theorem 7.1: ζ_p has a simple pole at
s=1, residue `1−p⁻¹`) and the *packaging* lemma (Lemma 7.5: `((1−φ∘ψ)F̃_a)(0)=−(1−p⁻¹)log_p(a)`),
but the target is an **unnumbered intermediate computation** that RJW dispatch in two
lines ("…collapses to −p⁻¹ log_p(a)"). No external work treats it as a citeable object.

Most general standard form: not applicable — the statement is fused to the project's
own objects (`FtildeA`, `seriesEval`, `extLog`), each of which is a project-specific
realisation of an RJW construction. There is no generality axis along which a
"maximally general" version is recognised in the literature; the result is *exactly*
the bookkeeping RJW needs for `p ∤ a`, an odd prime, over a field carrying `μ_p`.

Generality dimensions where the literature varies: none meaningful — `a`, the oddness,
`p∤a`, and the `μ_p`-carrying field are all intrinsic to the construction, not
incidental restrictions one would weaken.

Disagreement with the literature: none — the Lean statement faithfully transcribes
RJW's `φ∘ψ` step (with the project's bookkeeping that `(φ∘ψ F̃_a)(0)` equals
`(1/p)·Σ_i seriesEval(F̃_a)(ξⁱ−1)`, hence the sum here is `p·(−p⁻¹ log_p a) = −log_p a`).

**Signal.** The exhaustive sweep returned the *ambient* theorem and the *packaging*
lemma but **no independent name or standard form for the target**. Per the verdict
reference, literature naming the surroundings but not the step is a strong signal that
the decl is internal-construction bookkeeping — biasing Phase 7 toward BORDERLINE /
NO, never toward a standalone YES.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): there is **no standalone standard form**;
the target is an internal step. The closest *named* anchors are RJW Theorem 7.1
(the residue) and RJW Lemma 7.5 (the mass) — both downstream wrappers, both already
mirrored by *other* project decls.

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `K` complete ultrametric normed `ℚ_p`-algebra, CharZero, with `μ_p` | a field `K ⊇ ℚ_p(μ_p)` (e.g. ℂ_p) | RJW work over `ℂ_p` / a field containing `μ_p` | NO | `seriesEval` needs summability (ultrametric + complete); `μ_p ⊆ K` is essential to even *state* the sum; `extLog` is defined here. This *is* RJW's setting. |
| 2 | `hp2 : p ≠ 2` | p odd | RJW: p odd implicit (p−1≥2 used) | NO | `p−1 ≥ 2` is needed for exp-ball membership (`inExpBall_natCast_pow_sub_one`). Genuine. |
| 3 | `ha : p ∤ a` | p ∤ a | RJW: `a` a topological generator of `ℤ_p^×` (⇒ p∤a) | NO | `{ξᵃ}=μ_p` reindex *requires* `p∤a`; with `p∣a` the identity is false. Intrinsic. |
| 4 | `ha0 : a ≠ 0` | a ≠ 0 | implicit | NO | `u_0 = 0` makes the formal composition junk (`HasSubst` fails). Intrinsic. |
| 5 | `hξ : IsPrimitiveRoot ξ p` | ξ generates μ_p | RJW: ξ ∈ μ_p primitive | NO | The sum is *over* μ_p; the primitivity pins the indexing `i ↦ ξⁱ`. Intrinsic. |

#### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** *for what it is* — but "maximally general"
is the wrong frame here. Every hypothesis is intrinsic to RJW's construction; there is
no weakening to propose, and no broader literature form to aim at. The decl is not a
narrowed specialisation of anything; it is a fixed internal step.

Number of weakening opportunities found: **0**.
Proposed restatement: none.
Cost of restatement: n/a.

#### 4c. Modern mathlib-idiom check (Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already fully typeclass-driven (`NormedAlgebra`, `IsUltrametricDist`, …) | — |
| 2 | sequences/metric → filters/topological? | no | the sum is a finite `Finset.sum` over `Fin p`; `seriesEval` already uses `tsum` (a filter-limit). No sequence to filter-ise. | — |
| 3 | construct an object → universal-property class? | no | this is a *value identity*, not a construction. | — |
| 4 | set+closure-predicate → bundled substructure? | no | no substructure here. | — |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | no | already at the natural `NormedField`/`NormedAlgebra ℚ_p` level dictated by `extLog`/`seriesEval`. | — |
| 6 | 1-categorical → higher-categorical? | no | purely an analytic/algebraic computation. | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | the index `Fin p` *is* `μ_p`; the `a : ℕ` is genuinely a natural-number exponent. Not generalisable. | — |

Modern idiom available: **no.** One-line reason: the statement is an explicit finite
p-adic identity over the exact typeclass setting its constituent objects (`extLog`,
`seriesEval`, `FtildeA`) demand — there is no contemporary-idiom reorganisation that
composes with more of mathlib, because mathlib has none of these objects to compose with.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or
typeclass-search paths).

---

### PHASE 5 — Mathlib search (five-method)

#### Mathlib search-status: `PadicLFunctions.sum_seriesEval_FtildeA`

```
[A] Lean-Finder   n/a — MCP not available in this environment (substituted by D+web).
[B] Loogle        n/a — MCP not surfaced; substituted by structural grep over the
                  local mathlib checkout (.lake/packages/mathlib) for the building
                  blocks and for the constituent objects.
[C] LeanSearch    n/a — MCP not surfaced; substituted by WebSearch NL queries
                  (Phase 3 #1,#2,#5) and grep.
[D] Grep mathlib  searched: `padicLog`, `extLog`, `Kubota`, `pAdicLFunction`,
    src           `padic zeta`, `IwasawaLog`, p-adic `log_prod`, `Mahler*`,
                  cyclotomic `Πξ(Xξ−1)=Xⁿ−1`, `Real.log_prod`.
[E] Name pattern  searched repo-wide for `sum_seriesEval_FtildeA`, `seriesEval`,
                  `FtildeA`, `extLog`, `InExpBall`, `padicLog`.
```

Searched for both the user's current form and the (non-existent) literature-standard
form.

Findings:
- **`padicLog` is NOT in mathlib** — it is project-local (`PadicExp.lean:384`,
  `noncomputable def padicLog`). So are `extLog` (`ExtLog.lean:286`),
  `FtildeA`/`uA` (`ResidueZeta.lean:469`/`437`), `seriesEval` (`MeasureR/FormalPsi.lean:577`),
  `InExpBall` (`PadicExp.lean:65`).
- **Mathlib has NO p-adic L-function / Kubota–Leopoldt / residue-of-ζ_p machinery.**
  Grep over `Mathlib/NumberTheory/` for `Kubota`, `pAdicLFunction`, `padic zeta`
  returned nothing. The Lean-3 formalisation (arXiv 2302.14491) was never ported.
- Mathlib's only "Mahler" entries are `NumberTheory/MahlerMeasure.lean` (Northcott —
  unrelated) and `Padics/MahlerBasis.lean` (the Mahler basis of `C(ℤ_p, field)` — a
  building block, not the L-function transform).
- Mathlib **does** have the *individual* cyclotomic ingredient:
  `Polynomial.X_pow_sub_one_eq_prod` / `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`
  (`RingTheory/Polynomial/Cyclotomic/Basic.lean`), the `Πξ(Xξ−1)=Xⁿ−1` fact, used
  here *via* the project's `prod_erase_pow_twist`.
- Mathlib has `Real.log_prod` (`Analysis/SpecialFunctions/Log/Basic.lean:396`) — the
  **real**-valued "log of a product = sum of logs" — but **no p-adic analogue**;
  the project provides its own `padicLog_prod_of_norm_lt_one` (`ResidueZeta.lean:1289`),
  built from `MeasureR.padicLog_mul_of_norm_lt_one`.

Concluded: **not in mathlib** (all methods exhausted — including the constituent
objects and the literature framing). Mathlib cannot even *state* this theorem: the
objects `extLog`, `seriesEval`, `FtildeA` do not exist there, and there is no p-adic
L-function development to host it. Of the genuinely-mathlib ingredients, only the
cyclotomic product identity and `IsPrimitiveRoot` API are reused — everything p-adic-
analytic is project-local.

---

### PHASE 6 — Composition check (+ call-sites)

#### 6.0 Call sites — `PadicLFunctions.sum_seriesEval_FtildeA`

Internal use count: **K = 1** (within the project, excluding the declaring line).
External-to-file callers: 0 distinct files (the one caller is in the same file).
Cross-project callers: 0. The name is unique to `ResidueZeta.lean`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `ResidueZeta.lean:1595` | `rw [constantCoeff_FtildeA p K ha0, sum_seriesEval_FtildeA (p := p) K hp2 ha ha0 hξ] at hp_mul` — inside the proof of `constantCoeff_mahlerK_rhoA` (= RJW Lemma 7.5) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
(none) — the `μ_p`-trace is computed *only* here.

Call-sites reading: **K = 1 internal use, no inline re-derivation** → "possibly the
wrong abstraction / could be inlined" per the signal table — but here it is a
deliberate proof decomposition (a ~100-line step factored out of `constantCoeff_mahlerK_rhoA`),
not an accidental wrapper. The single consumer is the very next theorem (RJW Lemma 7.5).

#### 6a. Composition attempt

Can `sum_seriesEval_FtildeA` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1 (sketch): the proof is ~100 lines and chains **eight-plus project-local
lemmas** — `seriesEval_FtildeA_at_root`, `prod_erase_pow_twist`,
`padicLog_prod_of_norm_lt_one`, `extLog_eq_of_witness`,
`inExpBall_natCast_pow_sub_one`, `natCast_mul_seriesEval_uA`,
`norm_seriesEval_uA_sub_one_lt`, `constantCoeff_uA`, plus genuine reasoning
(`Finset.sum_sub_distrib`, the `erase 0` split because `u 0 = 1`, a product collapse
to `((a:K)^(p−1))⁻¹`, `field_simp`/`linear_combination`/`ring`).
  - Mathlib decls used: only peripheral (`Finset.*`, `IsPrimitiveRoot.*`, ring tactics).
  - Result: **fails** as a composition — the substance is project-specific.

Conclusion: **NOT-COMPOSABLE.** This is a real, substantial proof, not a 1–3-call
mathlib glue. (And the building blocks it composes are themselves project-local, so
even "inline at the call site" is impossible without first upstreaming `extLog`,
`seriesEval`, `FtildeA`, …)

---

## Verdict: `PadicLFunctions.sum_seriesEval_FtildeA`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): identified as the **unnumbered `φ∘ψ`-trace step inside
  the proof of RJW Lemma 7.5** (Rodrigues Jacinto–Williams, *An Introduction to
  p-adic L-functions*, §7). The literature names the surrounding Theorem 7.1 (residue
  `1−p⁻¹`) and the packaging Lemma 7.5, but gives the target itself no standalone name
  or standard form.
- Generality analysis (Phase 4): MAXIMALLY GENERAL *for what it is* — 0 weakenings;
  every hypothesis intrinsic. Phase 4c: no modern-idiom reformulation (nothing in
  mathlib to compose with).
- Mathlib search (Phase 5): **not in mathlib**, and *cannot* be — `extLog`,
  `seriesEval`, `FtildeA`, `padicLog`, and all p-adic L-function machinery are absent
  from mathlib; only the cyclotomic product identity + `IsPrimitiveRoot` API are
  genuinely reused.
- Composition check (Phase 6): **NOT-COMPOSABLE** (~100-line proof over 8+ project
  lemmas); call sites **K = 1**, no inline re-derivation, name unique to the file.

**Rationale.**
The decision genuinely turns on a judgment the skill cannot make from the evidence
alone, which is the definition of BORDERLINE. The clean buckets are all excluded:
it is **not `NO-mathlib-has-it`** (mathlib has nothing to redirect to — it cannot even
state the theorem); it is **not `NO-composable-from-mathlib`** (the proof is large and
its building blocks are themselves non-mathlib); and it is **not a clean YES**, because
(a) the target is not a standalone, literature-recognised statement — it is an internal
two-line step that RJW do not even number, and (b) it is welded to five project-specific
objects (`FtildeA`, `seriesEval`, `extLog`, `uA`, `InExpBall`) none of which exist in
mathlib. A `YES-add-as-is` verdict would also fail the Phase-7 gate's "name the concrete
mathlib gap" requirement: the only honest gap is "mathlib has no p-adic L-functions at
all", which is a *programme*, not a single-lemma contribution.

The real question is therefore upstream of this lemma: **should the whole p-adic
L-function / residue-of-ζ_p development (the `padicLog` + `extLog` + Mahler-transform
machinery this project builds) be contributed to mathlib?** If yes, this lemma rides
along as one private step of the `constantCoeff_mahlerK_rhoA` (Lemma 7.5) proof — almost
certainly inlined or kept `private`, *not* shipped as a standalone public API lemma
(K = 1, no external consumer, no independent name). If the development stays project-
local (the current AINTLIB posture — `ResidueZeta` is research-frontier work), this
decl is correctly project-internal as-is. That is a project-policy + mathlib-roadmap
call, not a mathematical one — hence BORDERLINE. This matches Case 5 in the verdict
reference (a project-specific analytic-number-theory bookkeeping result built on
non-mathlib objects, single internal use).

**Numbered questions (≤5):**

1. **Is the entire p-adic L-function development in `PadicLFunctions/` intended for
   eventual mathlib upstreaming**, or is it permanently project-local research-frontier
   work? (This is the gating question — every sub-verdict below depends on it.)
2. If upstreaming is intended: the foundational objects this lemma rests on —
   **`padicLog`, `extLog`, `seriesEval`, the Mahler-transform machinery** — are the
   true contributions and must go first. Should those be assessed/PR'd as a *batch*
   (e.g. via `/mathlibable` Mode B over `PadicExp.lean`, `ExtLog.lean`,
   `MeasureR/FormalPsi.lean`), with this lemma deferred until they land?
3. Even under upstreaming, this `φ∘ψ`-trace step has **K = 1 internal use, no external
   consumer, and no name in the literature**. Do you agree it should be **inlined into
   (or kept `private` to) the proof of `constantCoeff_mahlerK_rhoA` (RJW Lemma 7.5)**
   rather than shipped as a standalone public mathlib lemma?
4. If a packaged public result *is* wanted, the **citeable** RJW objects are
   **Theorem 7.1** (the residue, `1−p⁻¹`) and **Lemma 7.5** (the mass) — the project's
   downstream `constantCoeff_mahlerK_rhoA` / the residue theorem. Should the
   mathlibable effort target *those* named results, treating `sum_seriesEval_FtildeA`
   purely as supporting machinery?

**Next action:** user answers the questions; re-run `/mathlibable` if the upstreaming
decision flips the framing. Likely outcomes:
- *Permanently project-local* → drop from mathlib consideration; the decl is fine as-is
  (a deliberate, sorry-free proof decomposition).
- *Upstream the development* → this lemma becomes `private`/inlined supporting
  machinery; the real mathlibable work is the foundational `padicLog`/`extLog`/
  Mahler-transform layer (batch-assess those first) and the named RJW Theorem 7.1 /
  Lemma 7.5 results.

---

## Next step

User answers the four numbered questions (Q1 is gating: is the `PadicLFunctions`
development headed for mathlib at all?). If the answer reframes the verdict, re-run
`/mathlibable PadicLFunctions.sum_seriesEval_FtildeA`. Absent upstreaming, this decl is
correctly project-internal as-is; under upstreaming, assess the foundational
`padicLog`/`extLog`/`seriesEval` layer first and keep this `φ∘ψ`-trace step private to
the RJW-Lemma-7.5 proof.
