# `/mathlibable` report — `PadicLFunctions.constantCoeff_mahlerK_rhoA`

**Final five-bucket verdict: `BORDERLINE-needs-human`.**

One-line summary: a sorry-free, genuine piece of Kubota–Leopoldt p-adic
L-function mathematics (RJW Lemma 7.5 — the residue mass at `s=1`), but stated
entirely in project-local definitions (`mahlerK`, `rhoA`, `extLog`) that have
**no mathlib counterpart in any form**. It is neither already-in-mathlib nor a
≤3-call mathlib composition; whether it belongs in mathlib is inseparable from
whether the whole supporting construction is upstreamed — a roadmap judgment the
skill cannot make alone.

---

## Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task instruction); **reasoned from source** — the file is sorry-free and the target + its dependencies were read directly.
- decl `PadicLFunctions.constantCoeff_mahlerK_rhoA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:1587`
- kind:                      theorem
- has sorry:                 no (the whole file `ResidueZeta.lean` has 0 `sorry`; the target, its helper `constantCoeff_mahlerK_rhoA_eq_algebraMap`, and its consumer `zetaNum_one` are all sorry-free)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — proves RJW Theorem 7.1: simple pole of the trivial-character p-adic zeta function at s=1 with residue 1−p⁻¹.

---

## Statement (Phase 1)

`constantCoeff_mahlerK_rhoA` is **a theorem** stating the following:

Let `p` be an odd prime and `K` a complete, char-0, ultrametric normed field that
is a normed `ℚ_p`-algebra and contains a primitive `p`-th root of unity `ξ`
(in the application `K = ℂ_p`). Let `a` be a natural number with `p ∤ a`. Form the
measure `ρ_a` on `ℤ_p` — RJW's §4 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)`,
i.e. `PadicMeasure.zetaNum p a` pushed forward (`iota`) to `ℤ_p` and base-changed
to `K`. Apply the `K`-level Mahler/Amice transform `mahlerK` to obtain a power
series `𝓐(ρ_a) ∈ K⟦T⟧`. Then the **constant coefficient** of that power series —
the total mass of the measure — equals
$$ \operatorname{cc}\bigl(\mathcal A(\rho_a)\bigr) \;=\; -\Bigl(1 - p^{-1}\Bigr)\,\log_p(a), $$
where `log_p` is the project's *extended* (Iwasawa-branch, `log_p p = 0`)
p-adic logarithm `extLog`, evaluated at `(a : K)`. This is RJW Lemma 7.5
(TeX 2320), the "mass of `x⁻¹·Res(μ_a)`" in the §6 c₀-design form
`((1−φψ)F̃_a)(0) = −(1−p⁻¹)·log_p(a)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; `hp2 : p ≠ 2` restricts to odd primes.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]` — the ambient p-adic field (an extension of `ℚ_p` containing `μ_p`; instantiated at `ℂ_p`).
- `ξ : K`, `hξ : IsPrimitiveRoot ξ p` — a primitive p-th root of unity used in the explicit Σ-over-roots computation.

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — odd prime (the `(p−1)`-power Fermat witness and the exp/log ball estimates need `p ≥ 3`).
- `ha : ¬ (p : ℕ) ∣ a` — `a` is a p-adic unit (so `extLog (a : K)` is well-defined via the Fermat witness `a^{p−1}`).
- `ha0 : a ≠ 0`.

Conclusion (math): the total mass of the §4 numerator measure is `−(1−p⁻¹)·log_p(a)`.

Conclusion (Lean): `PowerSeries.constantCoeff (mahlerK p K (rhoA p K a)) = -(1 - (p : K)⁻¹) * extLog p ((a : K))`.

The four load-bearing names — `mahlerK`, `rhoA`, `extLog`, and (inside `rhoA`)
`MeasureR`/`zetaNum`/`iota`/`baseChange` — are **all project-local**:
- `extLog` — `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:286`
- `mahlerK` — `projects/PadicLFunctions/PadicLFunctions/MeasureR/FormalPsi.lean:749`
- `rhoA` — `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:651`
- `MeasureR` — `projects/PadicLFunctions/PadicLFunctions/MeasureR/Basic.lean:50`
- `zetaNum` — `projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/ZetaP.lean:74`
- `mahlerTransform` — `projects/PadicLFunctions/PadicLFunctions/MeasureR/MahlerTransform.lean:67`
- `padicLog` (underlying `extLog`) — `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:384`

---

## Size classification (Phase 2a)

Verdict: **BIG** (in the "main-result-adjacent" sense).
Reason: it is the key arithmetic input ("the mass") to RJW Theorem 7.1, the
project's main result for §7 (the residue/pole of the p-adic zeta function at
s=1). It is named after a literature lemma (RJW Lemma 7.5). It is *not* a new
structure (it is a `theorem`, not a `def`/`class`), but it is a headline
computation, not a throwaway helper.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

## One-line check (Phase 2b)

Body line count: 8 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not a `def`.** The one-liner
exemption table does not apply to theorems. (For the record the proof is a short
8-line glue: it invokes `p_mul_constantCoeff_mahlerK_rhoA`, rewrites two prior
results, then `field_simp; linear_combination` to divide by `p`. The substance
lives in the cited lemmas, not here — see the call-sites note in Phase 6.)

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic L-function residue at s=1 Kubota-Leopoldt Iwasawa measure log_p(a) mass formula" | yes | residue `1−p⁻¹` at `s=1` of the trivial-character KL p-adic zeta function; values at `s=1` connect to `log_p` of principal units (Iwasawa's formula) | Washington *Cyclotomic Fields*; Princeton AM-74 (Iwasawa); confirms the `1−p⁻¹` residue and the `log_p` link, but as theory, not this exact `cc` identity |
| 2 | WebSearch (general form / aliases) | "p-adic zeta function residue 1 - 1/p simple pole Iwasawa Mazur measure Amice transform" | yes | `ζ_{p,1}` is a pseudo-measure ⇒ simple pole at `s=1`, residue `1−p⁻¹`; Amice transform (Amice→Mazur) is the measure↔power-series dictionary | Colmez "Fontaine's rings and p-adic L-functions"; Rodrigues Jacinto–Williams; matches the *concept*, not the project's `extLog`-flavoured statement |
| 3 | WebSearch (mechanism / constant term) | "Mahler transform p-adic measure power series constant coefficient total mass Amice" | yes | "the constant coefficient of a Mahler series expansion encodes the **total mass** of a measure"; "measures on ℤ_p correspond to power series under the Mahler transform" | de Shalit *Mahler bases*; confirms cc(transform)=mass is the *standard* meaning of this object |
| 4 | WebSearch (source-text identification) | "\"p-adic L-function\" lecture notes Williams residue mass constant term Mahler transform measure log_p" | yes | Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions* (arXiv:2309.15692; Warwick notes) define `μ_a ↔ F_a(T)` under the Mahler transform and compute the residue | **This is "RJW"** — the project's source text. The Lemma-7.x numbering and TeX-line citations in the docstrings match these notes. |
| 5 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of the residue-mass identity") | **n/a** | — | ChatGPT MCP server is **not installed** in this environment (`/setup-chatgpt` not run). Substituted with WebSearch ×4 + nLab + direct mathlib-source grep. Recorded as a real gap, not skipped. |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | (no references dir) | Neither `.mathlib-quality/references/` nor a local `refs/` store exists in this checkout. The source paper is identified independently as RJW (channel 4). |
| 7 | nLab | "Iwasawa theory" (`ncatlab.org/nlab/show/Iwasawa+theory`) — fetched | partial | KL p-adic zeta via `g_i(v^s−1)=L_p(ω^{1−i},s)`; main conjecture framing | **No** explicit residue formula and **no** `cc(transform)=−(1−p⁻¹)·log_p(a)` on the page (verified by fetch). nLab treats the main conjecture, not this computation. |
| 8 | nCatLab / category-theoretic | (categorical reformulation of a measure-mass identity) | **n/a — not a categorical concept** | — | The statement is an explicit p-adic-analytic identity (constant coefficient of a power series = a logarithm). No universal property / categorical content to look up. |
| 9 | Stacks Project | (algebraic-geometry analog) | **n/a — not an algebraic-geometry concept** | — | Stacks covers schemes/stacks/commutative algebra; p-adic L-function residues and Iwasawa measures are out of scope. |
| 10 | MathOverflow / Math.SE | covered implicitly by channels 1–3 (the residue `1−p⁻¹` and "constant coefficient = mass" are textbook on MO/MSE) | yes | residue `1−p⁻¹` is the standard answer; "Amice/Mahler transform sends mass to constant term" is standard | No MO thread states this *exact* `extLog`-form identity as a named result; it lives inside constructions. |
| 11 | recent arXiv (last 5 yr) | "An introduction to p-adic L-functions" (arXiv:2309.15692, 2023) + de Shalit *Mahler bases* (JTNB 2016) | yes | the modern expository source; `μ_a ↔ F_a`, residue `1−p⁻¹`, mass via constant term | Confirms the content is current-standard textbook material, **embedded in the KL construction**, never isolated as a reusable lemma about an abstract `mahlerK`. |

### Literature summary (Phase 3)

Concept identified as: the **total mass / constant Mahler(=Amice) coefficient of
the numerator measure** in the Kubota–Leopoldt construction of the p-adic zeta
function — the arithmetic engine of the **residue `1−p⁻¹` at `s=1`** (RJW Lemma
7.5). Source text: **Rodrigues Jacinto–Williams, *An introduction to p-adic
L-functions*** (arXiv:2309.15692) = "RJW", with de Shalit's *Mahler bases* and
Washington's *Cyclotomic Fields* / Iwasawa's AM-74 as the classical backdrop.

Sources agree on the standard form: **yes** for the *mathematics* — the residue is
`1−p⁻¹`; the constant coefficient of the transform is the total mass; and values
at `s=1` are governed by `log_p`. There is no disagreement on content.

Most general standard form: the residue/mass result is always stated *inside* a
specific construction (a specific measure `μ_a`, a specific transform). There is
**no** literature statement of an abstract reusable lemma "for any base-changed
pushforward of `zetaNum`, the constant coefficient of its `K`-Mahler transform is
`−(1−p⁻¹)·extLog a`". The object `mahlerK (rhoA p K a)` and the *extended*
(Iwasawa-branch) `extLog` are the project's own packaging.

Generality dimensions where the literature varies:
  - the **branch of `log_p`**: classically one fixes `log_p p = 0` (Iwasawa branch) — the project's `extLog` is exactly this, generalised to a junk-total function on rational-valuation elements; mathlib's `padicLog`/`padicExp` do not exist at all (see Phase 5).
  - the **coefficient ring/field**: RJW works over `ℚ_p` (or `ℂ_p` for the roots-of-unity step); the project works over a general such `K` and descends — a presentational choice, not a literature-standard generality axis.

Disagreement with the literature: **none on mathematics.** The only "gap" is
organisational: the literature has no named, reusable, abstract version of this
identity — it is a construction-internal computation. That bears directly on the
verdict (it is not a recognised standalone theorem to upstream as-is).

---

## PHASE 4 — Generality analysis

### Generality analysis — `constantCoeff_mahlerK_rhoA`

Literature-standard form (from Phase 3): the residue `1−p⁻¹` / the mass
`−(1−p⁻¹)·log_p(a)` of the numerator measure, as it appears *inside* the KL
construction over `ℚ_p`/`ℂ_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `K` (complete ultrametric char-0 normed `ℚ_p`-algebra with `μ_p`) | a general such field, used at `ℂ_p` | RJW computes in `ℂ_p`, descends to `ℚ_p` | already general | This is already *more* general than the literature's concrete `ℂ_p`; it is the right level for the descent. Not a narrowing. |
| 2 | `hp2 : p ≠ 2` | odd prime | RJW assumes `p` odd throughout §7 | NO | The Fermat-witness `a^{p−1}` and the exp/log convergence-ball estimates genuinely need `p ≥ 3`; matches the literature restriction. |
| 3 | `ha : ¬ p ∣ a`, `ha0 : a ≠ 0` | `a` a p-adic unit | `a` ranges over the units used to build `μ_a` | NO | `extLog (a:K)` is defined via `a^{p−1}` being a 1-unit; `p ∤ a` is exactly what makes `log_p a` meaningful. Matches literature. |
| 4 | `ξ`, `IsPrimitiveRoot ξ p` | explicit primitive p-th root | RJW's roots-of-unity step | NO | Intrinsic to the Σ-over-roots collapse in the proof; the statement quantifies it as a hypothesis, exactly as the literature argument requires. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** for what it is (it already runs over a
general `K` rather than fixing `ℂ_p`, and every hypothesis matches the
literature's restrictions). 
Number of *weakening* opportunities found: 0.

**BUT this is not the operative axis.** The form is not "narrow vs. general" — it
is *project-local vs. mathlib-ready*. Its conclusion and every name in it
(`mahlerK`, `rhoA`, `extLog`) are project definitions absent from mathlib. The
generality question ("could we weaken a hypothesis?") is moot until the prior
question ("is the vocabulary mathlib's?") is answered — and Phase 5 answers it
"no". So there is no "generalise-first restatement" to propose: the blocker is the
missing supporting library, not an over-strong hypothesis.

Cost of (hypothetical) restatement against mathlib vocabulary: **EXPENSIVE** — it
would require first upstreaming `MeasureR`, the Mahler/Amice transform, `extLog`,
and the `zetaNum`/KL scaffolding. (Per the skill, EXPENSIVE is not itself a
downgrade; it is recorded for sequencing.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | `K`'s hypotheses are already a clean typeclass cluster (`NormedField`+`NormedAlgebra ℚ_[p]`+`IsUltrametricDist`+`CompleteSpace`+`CharZero`); `rhoA`/`mahlerK` are already bundled | already idiomatic |
| 2 | sequences/metric → filters/topology? | no | the statement is an algebraic identity of power-series coefficients; no limit is taken here (limits live in the *sibling* residue theorem, not this lemma) | n/a |
| 3 | explicit construction → universal property? | partial-but-no | `mahlerK`/the Amice transform *is* an isomorphism `Measures ≃ power series` (de Shalit); a universal-property packaging would belong to the **transform's** mathlib upstreaming, not to this individual mass-identity | the whole Amice-transform API — but that is a separate, prior contribution |
| 4 | set+closure predicate → bundled substructure? | no | no substructure here | n/a |
| 5 | field/metric-specific → weaken typeclasses? | no | already at the natural p-adic-field level; weakening below "complete ultrametric `ℚ_p`-algebra" loses the convergence the proof needs | n/a |
| 6 | 1-categorical → higher-categorical? | no | not a categorical statement | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid/group? | no | the only index is the prime `p` and the unit `a`; both are intrinsic | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this* declaration). The decl is already at a
clean, idiomatic level given its vocabulary. The one genuine "modernisation"
opportunity (row 3) is about upstreaming the **Amice/Mahler transform as a
characterised isomorphism** — that is a property of the *infrastructure*
(`mahlerK`/`MeasureR`), a separate and prior contribution, and does not turn this
specific mass-identity into a different-shaped reusable lemma. There is no
contemporary mathlib formulation that re-shapes `cc(mahlerK(rhoA a)) = …` into
something composing with existing mathlib API, because the existing mathlib API
for p-adic measures-as-power-series does not exist.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities and no typeclass-search paths, so the six-row diamond/defeq table does
not apply.

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.constantCoeff_mahlerK_rhoA`

[A] **Lean-Finder**   — *n/a: MCP/web tool not installed in this environment.* Substituted by exhaustive local grep over the full mathlib tree at `./.lake/packages/mathlib/Mathlib` (methods D/E below), which is the authoritative source-of-truth substitute.
[B] **Loogle**        — *n/a: `lean_loogle` MCP not installed.* The decisive type-pattern search would be `PowerSeries.constantCoeff _ = _ * _` over p-adic measures, but the load-bearing constituents (`mahlerK`, `rhoA`, `extLog`) are not mathlib symbols, so any Loogle pattern would necessarily miss; the question is settled by D/E.
[C] **LeanSearch**    — *n/a: `lean_leansearch` MCP not installed.* Natural-language intent ("constant coefficient of Mahler transform of p-adic measure equals p-adic log") maps onto concepts confirmed absent below.
[D] **Grep mathlib src** — ran ≥6 targeted greps over `./.lake/packages/mathlib/Mathlib`:
   - `padicLog` / `padicExp`  → **0 hits** (the only log/exp neighbour is `Analysis/SpecialFunctions/Log/ENNRealLogExp.lean`, the *extended-nonneg-reals* log, entirely unrelated). The extended/Iwasawa-branch p-adic logarithm **does not exist in mathlib**.
   - `extLog` / `ExtLogDomain` → **0 hits.**
   - `MeasureR` / p-adic measure on `ℤ_[p]` / `IwasawaAlgebra` / `Mazur.*measure` / `Amice` → **0 hits.** Mathlib has **no** measures-on-ℤ_p / Iwasawa-algebra / Amice-transform machinery.
   - `zetaNum` / `rhoA` / p-adic L-function / `KubotaLeopoldt` → **0 hits** for the construction. (`Iwasawa.lean` exists but is `GroupTheory/GroupAction/Iwasawa` — Iwasawa decompositions of groups, unrelated.) Mathlib has Riemann/Hurwitz/Dirichlet zeta (`NumberTheory/LSeries/`) but **no p-adic L-function / KL zeta**.
   - `mahler` → hits `NumberTheory/Padics/MahlerBasis.lean` and `NumberTheory/MahlerMeasure.lean`. **Read both.** `MahlerBasis` provides the Mahler **basis** isometry `mahlerEquiv : C(ℤ_p,E) ≃ₗᵢ[ℤ_p] C₀(ℕ,E)` (`mahler`, `mahlerSeries`, `mahlerTerm`) — i.e. continuous functions ↔ coefficient sequences. It does **not** provide the dual **measures → power-series** Amice/Mahler transform, and has no constant-coefficient-as-mass lemma. `MahlerMeasure` is the unrelated *polynomial* Mahler measure `∏ max(1,|root|)`.
   - `PowerSeries.constantCoeff` → exists as the generic ring-hom `PowerSeries.constantCoeff` (`RingTheory/PowerSeries/Basic.lean:137`) with the expected `_zero/_one/_C/_smul` API. This is the **only** mathlib primitive appearing in the target's statement (with `Nat.cast`). It is a coefficient extractor, not the result.
[E] **Name pattern** (grep over mathlib for the relevant stems) — `mahlerK`, `rhoA`, `constantCoeff_mahler*`, `extLog`, `zetaNum` → **0 hits** in mathlib (all resolve only inside `projects/PadicLFunctions/`).

Searched for both:
  - the user's current form (`cc(mahlerK(rhoA a)) = −(1−p⁻¹)·extLog a`) — absent;
  - the literature-standard content (residue `1−p⁻¹`; mass = constant Amice coefficient; KL p-adic zeta) — the *construction* on which it depends is entirely absent from mathlib.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). Stronger than "not found": the statement is **not even
expressible** in mathlib's current vocabulary — every non-`PowerSeries.constantCoeff`,
non-`Nat.cast` symbol in it (`mahlerK`, `rhoA`, `extLog`, and transitively
`MeasureR`/`mahlerTransform`/`zetaNum`/`iota`/`baseChange`) is a project-local
definition with no mathlib analog.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `constantCoeff_mahlerK_rhoA`

Internal use count: **K = 1** (within the project, excluding the declaring block).
External-to-file callers: **0** distinct files (no downstream/other-project consumer).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ResidueZeta.lean:1678 | `rw […, constantCoeff_mahlerK_rhoA (p := p) ℂ_[p] hp2 ha ha0 hξ, map_mul, …]` — single rewrite step inside `zetaNum_one` (the descent theorem), specialised to `K = ℂ_p` |

Inline-derivation grep (was the identity re-derived elsewhere without using this lemma?): **(none)** — no other proof reconstructs `cc(mahlerK(rhoA a))` inline; the sole consumer goes through this lemma.

What the call-sites pattern tells you: `K = 1` internal use, no external use, no
inline re-derivation → per the Phase-6 table this is the "K = 1 internal use only
→ possibly the wrong grain; could be inlined" signal. Here it is the single
arithmetic input to `zetaNum_one`. It is **not** dead code and **not** a
mathlib-bypassing wrapper (mathlib has nothing to bypass); it is a genuine
intermediate step in one construction. The low call count reinforces that, *in its
current project-local form*, it is construction-internal scaffolding rather than a
broadly-reused public API.

### Composition check (Phase 6)

Can `constantCoeff_mahlerK_rhoA` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: any mathlib-only derivation of `cc(mahlerK(rhoA a)) = −(1−p⁻¹)·extLog a`.
  - Mathlib decls used: `PowerSeries.constantCoeff` (+ `Nat.cast`) — and **nothing else applies**, because `mahlerK`, `rhoA`, and `extLog` are not mathlib objects.
  - Result: **fails immediately** — you cannot even *write* the statement using only mathlib decls. There is no mathlib `mahlerK`, no `rhoA`, no `extLog` to compose.
  - Notes: the actual project proof is itself an 8-line glue over **project** lemmas (`p_mul_constantCoeff_mahlerK_rhoA`, `constantCoeff_FtildeA`, `sum_seriesEval_FtildeA`), each of which is in turn a substantial multi-hundred-line development — far beyond a 3-call mathlib composition.

Attempt 2: derive it as a 1–3 call composition of the *project's own* lemmas (i.e. is it a trivial wrapper over existing project API)?
  - Even restricted to project lemmas it is a `rw` of two prior results plus `field_simp; linear_combination` — a genuine (if short) proof, and those two prior results (`constantCoeff_FtildeA`, `sum_seriesEval_FtildeA`) are themselves hard theorems. Not a trivial alias.

Conclusion: **NOT-COMPOSABLE** from mathlib (the statement is not even mathlib-expressible; a fortiori not a ≤3-call mathlib composition).

---

## PHASE 7 — Verdict

## Verdict: `PadicLFunctions.constantCoeff_mahlerK_rhoA`

**Category: `BORDERLINE-needs-human`**

**Evidence:**
- Literature search (Phase 3): the *mathematics* is classical/standard (residue `1−p⁻¹`; constant Amice/Mahler coefficient = total mass; values at `s=1` via `log_p`) — source text RJW (arXiv:2309.15692), backdrop Washington/Iwasawa/de Shalit. **But the literature has no named, reusable, abstract version** of `cc(mahlerK(rhoA a)) = −(1−p⁻¹)·extLog a`; it is always a construction-internal computation.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for its vocabulary (0 weakenings; already runs over a general `K`, not fixed `ℂ_p`); modern-idiom check found no re-shaping of *this* lemma. The operative axis is project-local-vs-mathlib-ready, not narrow-vs-general.
- Mathlib search (Phase 5): **not in mathlib**, and *not expressible* in mathlib — `mahlerK`, `rhoA`, `extLog` (and the whole `MeasureR`/Amice-transform/`zetaNum`/KL stack) are absent; mathlib has neither `padicLog`/`padicExp` nor any p-adic L-function machinery.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib; K=1 internal call site, 0 external, no inline re-derivation.

**Rationale (1–2 paragraphs):**

This is real, sorry-free, literature-grounded p-adic L-function mathematics — RJW
Lemma 7.5, the mass that produces the `1−p⁻¹` residue of the trivial-character
Kubota–Leopoldt p-adic zeta function at `s=1`. It is not junk, not a duplicate,
and not a trivial wrapper. The reason it cannot be assigned a YES or a NO bucket
on its own is structural: the declaration is stated entirely in terms of
project-local definitions (`mahlerK`, `rhoA`, the *extended* `extLog`) for which
mathlib has **no counterpart in any form**. So `NO-mathlib-has-it` is false
(mathlib has nothing), `NO-composable-from-mathlib` is false (you cannot inline it
at a call site using ≤3 mathlib calls — you cannot even express it with mathlib
decls), and `YES-add-as-is` is *premature* (you cannot add a theorem whose
statement references four definitions that are not in mathlib). The decl is
inseparable from its supporting construction.

The genuine judgment call — the one the skill must hand to a human — is therefore
**roadmap-level**: does the AINTLIB project intend to upstream the whole
Kubota–Leopoldt / Amice-transform / `extLog` apparatus to mathlib? Two facts make
this a real fork rather than an obvious "no": (a) mathlib currently has **none** of
this (no `padicLog`, no p-adic L-functions, no Iwasawa measures), so the
construction would be a large, valuable, genuinely-new contribution if pursued;
and (b) the def-first siblings already assessed in this same batch point internal
— `rhoA` → `NO-composable-from-mathlib`, `FtildeA` → `NO-composable-from-mathlib`,
`psi_rhoA` → `BORDERLINE` — i.e. the supporting definitions are themselves being
treated as project-internal scaffolding, not as imminent mathlib API. A theorem
*about* those definitions cannot rationally be graded YES while the definitions it
mentions are graded NO/BORDERLINE. The verdict for this lemma is thus bound to,
and slightly downstream of, the decision about the construction as a whole. That
decision is mathematical-roadmap taste, not something Phases 3–6 can settle —
hence BORDERLINE, with the questions below.

**Numbered questions (≤5):**

1. **Is the entire `MeasureR` / Mahler-(Amice-)transform / `extLog` / Kubota–Leopoldt
   apparatus intended for mathlib upstreaming?** If yes, this lemma rides along with
   that effort and becomes a `YES`-class item *stated against the upstreamed
   definitions* (likely after the transform is packaged as a characterised
   isomorphism, per Phase 4c row 3). If no, it stays project-local permanently.
2. **Is `extLog` (the junk-total, Iwasawa-branch extended logarithm) the form you
   intend to upstream, or is it a project-internal convenience?** Mathlib has no
   `padicLog`/`padicExp` at all; the mathlib-worthy primitive is almost certainly a
   clean `padicLog`/`padicExp` (+ a domain-restricted extension), and this lemma
   should be restated against *that*, not against the bespoke `extLog`, before any PR.
3. **Should the headline contribution be the abstract Amice/Mahler transform
   `Measures(ℤ_p) ≃ K⟦T⟧` with "constant coefficient = total mass" as a general
   lemma** (de Shalit's framework), with this `rhoA`-specific identity then a short
   corollary — rather than upstreaming the specific identity directly? (This is the
   Phase-4c row-3 question: package the infrastructure first.)
4. **Is the `−(1−p⁻¹)·log_p(a)` mass wanted as a standalone reusable result, or only
   as the internal step it currently is** (single call site, inside `zetaNum_one`)? If
   only internal, it need not be a separate mathlib lemma even after the construction
   is upstreamed — it could be inlined into the residue theorem.

**Next action:** user answers the questions; re-run `/mathlibable
PadicLFunctions.constantCoeff_mahlerK_rhoA` to resolve. Likely outcomes:
- "construction is **not** headed to mathlib (project-internal)" → drop from mathlib
  consideration; keep as project-local scaffolding (consistent with the `rhoA` /
  `FtildeA` sibling verdicts).
- "construction **is** headed to mathlib" → this becomes `YES-but-generalise-first`,
  where the *generalisation* is (i) restating against a clean upstreamed
  `padicLog`/`padicExp` instead of the bespoke `extLog`, and (ii) sequencing it
  after the Amice/Mahler transform is contributed as characterised API; the present
  proof would be re-derived on top of the upstreamed primitives.

---

## Next step

User answers the four numbered questions above (chiefly: *is the Kubota–Leopoldt /
Amice-transform / `extLog` construction being upstreamed to mathlib?*), then re-run
`/mathlibable PadicLFunctions.constantCoeff_mahlerK_rhoA`. As a standalone
declaration in its current project-local vocabulary it cannot be added to mathlib;
whether it *should* be — and in what restated form — is a roadmap decision bound to
the fate of its supporting library, which the skill cannot make alone.
