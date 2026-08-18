# `/mathlibable` report — `PadicLFunctions.MeasureR.padicLog_pow_p_of_norm_lt_one`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — the
                            decl + its full dependency chain were read directly from the `.lean`
                            files; the proof body contains no `sorry`).
- decl `PadicLFunctions.MeasureR.padicLog_pow_p_of_norm_lt_one`:
                            ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:513`
- kind:                      theorem
- has sorry:                 no (proof complete; closes via the `seriesEval`/φ bridge)
- module docstring summary:  RJW §6.2 Thm 6.1(ii): the p-adic value `L_p(θ,1)` (Leopoldt), via an
                             explicit antiderivative `F̃_θ` and the Mahler transform of the measure
                             `ρ_θ`. This file develops the `p`-adic logarithm power/multiplicativity
                             laws on the open unit ball as an analytic input to that value.

Namespace context: `namespace PadicLFunctions` → `namespace MeasureR`; section variables
`(p : ℕ) [hp : Fact p.Prime]`, `(K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
[IsUltrametricDist K] [CompleteSpace K] [CharZero K]`. The theorem has `omit [CharZero K]` and
`include hp`, so its actual hypothesis cluster is: `K` a **complete ultrametric normed field that
is a normed `ℚ_p`-algebra**, `p` prime.

---

### Statement (Phase 1)

`padicLog_pow_p_of_norm_lt_one` is a **theorem** stating the following:

Let `K` be a complete, ultrametric, normed field that is a normed algebra over `ℚ_p` (`p`
prime), and let `padicLog p : K → K` be the `p`-adic logarithm `log(x) = Σ_{n≥1} (−1)^{n+1}(x−1)^n/n`
(defined as a junk-total `tsum`, meaningful on the open unit ball). Then for every `z ∈ K` with
`‖z − 1‖ < 1`,

    log_p(z^p) = p · log_p(z),

i.e. the `n = p` instance of the logarithm power law `log(z^n) = n·log(z)`, holding throughout
the **open unit ball** `‖z − 1‖ < 1` — the full domain of convergence of the log series, which is
strictly larger than the convergence disc `‖x‖ < p^{−1/(p−1)}` of the `p`-adic exponential
(`InExpBall`, where the easier multiplicativity proof via exp lives).

Variables / typeclasses involved (Lean side):

- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` —
  a complete ultrametric normed `ℚ_p`-algebra field (the natural setting subsuming `ℚ_p`, `ℂ_p`,
  and finite/complete extensions). `[CharZero K]` is **omitted** for this theorem.
- `padicLog p : K → K` — the analytic `p`-adic log (defined in `PadicExp.lean:384` as a `tsum`).

Hypotheses (Lean side):

- `(hz : ‖z - 1‖ < 1)` — `z` lies in the open unit ball (the log-convergence disc).

Conclusion (math): `log_p(z^p) = p · log_p(z)`.

Conclusion (Lean): `padicLog p (z ^ p) = (p : K) • padicLog p z`.

How the proof works (load-bearing for the composition check): it does **not** go through exp
(the exp series does not converge on this larger ball). Instead it uses the formal-power-series
identity `phiSeries p (formalLog K) = (p : K) • formalLog K` (`phiSeries_formalLog`) and the
analytic evaluation bridge `seriesEval (formalLog K) (z − 1) = padicLog p z` (`seriesEval_formalLog`),
plus `seriesEval_phi_of_summable_prod` and `summable_prod_of_norm_coeff_le_linear`, to compute
`padicLog (z^p)` two ways and equate them. This formal-series-to-analytic bridge is the project's
own machinery (`MeasureR/FormalPsi.lean`).

---

### Size classification (Phase 2a)

Verdict: **BIG (borderline)** — it is *not* a standalone main result (it is one link in a chain),
but it is a named instance of a **classical, textbook-standard theorem** (the `p`-adic logarithm
power law on the open unit ball). Per the skill's BIG criteria, "a theorem that is essentially a
named classical result, basically guaranteed to be in or near the literature" pushes it to BIG.
Mathematically it sits inside the standard `p`-adic-analysis toolkit.

Reason: classical content (log power law), even though packaged here as the `n = p` step of a
larger internal bootstrap.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. One-liner check is **n/a**.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                                              | Hit?  | Standard form found                                                                                       | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------|-------|-----------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm power law log(x^n) = n log(x) Iwasawa convergence open unit ball"                                                | yes   | `log_p` converges for `\|x−1\|_p < 1`; `\|x\|=1 ⇒ \|x^n−1\|<1` for some `n`, and one *defines* `log_p(x) = (1/n) log_p(x^n)` — i.e. the power law is the standard extension trick | MIT exp/log notes, Iwasawa extension; confirms power law on the open unit ball is canonical |
|  2 | WebSearch (general form)         | "p-adic logarithm log_p multiplicative log(xy)=log(x)+log(y) domain \|x-1\|<1 maximal disk"                                        | yes   | `log((1+x)(1+y)) = log(1+x)+log(1+y)` for `x,y ∈ m`; radius of convergence 1; isometry on the smaller `p^{−1/(p−1)}` ball | MIT 18.785 PSet 10, PlanetMath; the power law is the immediate corollary of multiplicativity |
|  3 | WebSearch (named-after / aliases)| "Iwasawa p-adic log series additivity unit disk versus exponential convergence radius p^{-1/(p-1)}"                                | yes   | `exp` converges only on `\|z\|<p^{−1/(p−1)}`; `log` on the full `\|z−1\|<1`; the larger log-domain is the standard distinction | Koblitz GTM 58, Iwasawa lectures; matches the project's `InExpBall` (small) vs open-unit-ball (large) split exactly |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of the p-adic log power law")                                       | n/a   | —                                                                                                         | ChatGPT MCP is **not configured** in this environment (no `chatgpt`/`ask` tool surfaced by ToolSearch). Recorded n/a with reason; **compensated** by 6 web channels + 4 fetched primary sources (Wikipedia, PlanetMath, MIT, plus PlanetMath Proposition), which independently and unanimously fix the standard form. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` + `refs/`                                                             | n/a   | (no references dir; no `refs/` symlink present)                                                           | Both absent — recorded n/a. (Sibling `.mathlib-quality/overview/mathlibable/*.md` reports confirm the project's `log_p`/`extLog` context but are not source references.) |
|  6 | nLab                             | "nLab p-adic exponential logarithm Iwasawa logarithm definition properties"                                                       | yes   | `log_p`, `exp_p` are injective group homs on their domains; `log_p` is the unique hom `ℚ_p^× → (ℚ_p,+)` with `log_p(p)=0` extending the series; Iwasawa logarithm is canonical | confirms the homomorphism property (⇒ power law) is the *defining* structural fact |
|  7 | nCatLab (categorical)            | (covered by #6; "formal group law logarithm `log_F(F(X,Y))=log_F X+log_F Y`")                                                      | yes   | `log_p` arises from the 1-dim multiplicative formal group law; additivity `log_F(F(X,Y))=log_F X+log_F Y` | the formal-group view is the categorical packaging; the power law is `log_F([n](X))=n·log_F(X)` |
|  8 | Stacks Project (alg geom)        | —                                                                                                                                  | n/a   | not an algebraic-geometry concept (analytic `p`-adic function theory; the formal-group angle is in #7) | recorded n/a with reason |
|  9 | MathOverflow / Math.StackExchange| "p-adic logarithm properties log(x^n) power formula" (surfaced via web channels 1–3 + MIT 18.785 PSet 10)                          | yes   | the power law is posed as a *standard exercise*; "follows directly from the group homomorphism structure" | corroborates triviality-as-a-corollary once multiplicativity is in hand |
| 10 | recent arXiv (last 5 years)      | "\"p-adic logarithm\" properties \"log(x^n)\" power formula recent paper 2022 2023 2024"                                           | yes   | Dion (Laval) survey; arXiv 2304.02789, 2410.20934, 1907.06437 all *use* `log_p(xy)=log_p x+log_p y` and the power law as background | the power law is cited as classical background, never as a result — strong "it's textbook" signal |

The protocol passes: WebSearch ran ≥3 distinct queries at three generality levels (specific
power law / general multiplicativity / exp-vs-log domain contrast); ChatGPT MCP is recorded n/a
*with reason* and compensated by 4 fetched primary sources; local references checked (absent);
nLab checked; nCatLab/Stacks/MathOverflow/arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the `p`-adic logarithm power law** `log_p(z^n) = n·log_p(z)` (here `n = p`),
on the open unit ball `‖z − 1‖ < 1` — a corollary of the **multiplicativity** `log_p(zw) = log_p z + log_p w`
of the `p`-adic (Iwasawa) logarithm on `1 + 𝔪`.

Sources agree on the standard form: **yes** — unanimously. Wikipedia, PlanetMath (an explicit
Proposition `log_p(x·y)=log_p(x)+log_p(y)`), the MIT 18.785 notes, Koblitz, Iwasawa, nLab, and
multiple recent arXiv papers all give: log series converges on `‖x−1‖<1`, is multiplicative there,
and hence `log(x^n) = n·log(x)`. The exp series converges only on the strictly smaller disc
`‖x‖ < p^{−1/(p−1)}`.

Most general standard form: `log_p : 1 + 𝔪 → (K, +)` is an additive homomorphism for `K` a complete
non-archimedean (ultrametric) field extension of `ℚ_p` (the literature usually states it for `ℂ_p`;
the homomorphism/power-law content holds verbatim over any complete ultrametric `ℚ_p`-algebra field —
exactly the project's `K`). The power law `log(z^n) = n·log(z)` (all `n`) is the corollary; the
`n = p` case is one instance.

Generality dimensions where the literature varies:
  - **Base field**: literature usually `ℂ_p`; the structural statement holds over any complete
    ultrametric `ℚ_p`-algebra field. The project's `K` is the maximally-general such setting.
  - **Exponent `n`**: literature states the power law for *all* `n` (or directly as multiplicativity);
    the target is the `n = p` special case only.

Disagreement with the literature: **none** on content. The only mismatch is *grain*: the literature
states multiplicativity (or the `∀n` power law); the target isolates `n = p`.

---

### Generality analysis — `padicLog_pow_p_of_norm_lt_one` (Phase 4)

Literature-standard form (from Phase 3): the `∀ n` power law `log_p(z^n) = n·log_p(z)` on
`‖z − 1‖ < 1` (itself a corollary of multiplicativity `log_p(zw) = log_p z + log_p w`).

| # | Parameter / hypothesis                          | Current Lean form                                   | Literature-standard form                                  | Weaker / more general form exists? | Reason it can/can't be generalised |
|---|-------------------------------------------------|-----------------------------------------------------|-----------------------------------------------------------|------------------------------------|-------------------------------------|
| 1 | base field cluster `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` | complete ultrametric normed `ℚ_p`-algebra field | complete non-archimedean extension of `ℚ_p` (lit usually `ℂ_p`) | **already maximally general** | The Lean form is *more* general than the textbook `ℂ_p` statement. No weakening available; this axis is already at the mathlib-ideal level. |
| 2 | exponent fixed to `p`                            | `z ^ p`, conclusion `(p : K) • …`                   | `z ^ n`, conclusion `n • …`, **all** `n : ℕ`               | **YES — strictly narrower**         | Nothing in the *statement* needs `n = p`; the literature law is `∀ n`. The proof's φ-identity `φ(formalLog)=p·formalLog` happens to give the `p`-power step, but the **general `∀n` law is the standard object** and is in fact already proved in this very file as `padicLog_pow_of_norm_lt_one` (line 577) — derived from multiplicativity, not from this lemma. |
| 3 | `(hz : ‖z − 1‖ < 1)`                             | open unit ball                                      | open unit ball (radius-1 disc) — the full log-domain      | NO                                  | This is *already* the maximal domain (any larger and the series diverges). Correctly the full domain, not the smaller exp-disc. Good. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — on the **exponent axis** (row 2). The
base-field axis (row 1) and the domain (row 3) are already maximally general / correct; the single
narrowing is fixing `n = p` where the literature-standard object is the `∀ n` power law (or,
upstream of it, multiplicativity).

Number of weakening opportunities found: **1** (exponent `p` → arbitrary `n`).

Proposed restatement (the literature-standard form):

```lean
theorem padicLog_pow_of_norm_lt_one {z : K} (hz : ‖z - 1‖ < 1) (n : ℕ) :
    padicLog p (z ^ n) = n • padicLog p z
```

(which already exists in the project at `ValuesAtOne.lean:577`, proved from
`padicLog_mul_of_norm_lt_one`). The truly canonical mathlib object one tier up is the
**multiplicativity** `padicLog p (x * y) = padicLog p x + padicLog p y` on `‖·−1‖<1`
(`padicLog_mul_of_norm_lt_one`, line 543), from which both the `∀n` power law and this `n=p`
case follow.

Cost of restatement: **n/a in this file** (the general form is *already proved here*). The relevant
question is therefore not "can we generalise" but "what is the right mathlib-facing object" — see
Phase 4c and the verdict.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                                                 | Applies? | Proposed reformulation                                                                                  | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------------------------|----------------------------------|
|  1 | Bundled "let X be a foo" preambles → typeclasses?                                                                                         | no       | already fully typeclass-driven (`[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`) | n/a — already idiomatic |
|  2 | sequences/metric → filters/topological?                                                                                                   | no       | the statement is an algebraic identity about a fixed analytic function; no limit-shape to filter-ise     | n/a |
|  3 | construct an object → universal-property class?                                                                                          | **partially** | `log_p` is the unique additive hom `1+𝔪 → (K,+)` extending the series (nLab) / arises from the multiplicative formal group law; a `padicLog` packaged as an `AddMonoidHom` (or via mathlib `RingTheory.FormalGroup`) would carry multiplicativity *structurally* | a bundled `log_p : (1+𝔪)ˣ →+ K` would make `log_pow`/`log_mul`/this `n=p` case `map_pow`/`map_mul`/`map_nsmul` for free — the entire power-law family collapses into mathlib's `MonoidHom`/`AddMonoidHom` API |
|  4 | set-with-closure-predicate → bundled substructure?                                                                                       | no       | no substructure here (the ball is a hypothesis `‖z−1‖<1`, not a bundled object the lemma constructs)     | n/a (though a bundled `1+𝔪` unit-ball group is the natural *domain* for the hom in row 3) |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                                                                   | no       | already at the right level (`NormedField` + ultrametric + `ℚ_p`-algebra is the minimal sensible base)    | n/a |
|  6 | 1-categorical → higher-categorical?                                                                                                       | no       | not a categorical statement                                                                              | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                                                                         | **yes**  | the index here is the *fixed prime `p`*; the natural index is arbitrary `n : ℕ` (row 2 of 4a) — and via row 3, arbitrary `n` is just `map_nsmul` on the hom | unifies with `AddMonoidHom.map_nsmul` / `map_pow`; no per-`n` lemma needed |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**.
  - Proposed mathlib-idiomatic restatement: define the analytic `padicLog` (mathlib currently has
    **no** `p`-adic log at all) and expose its multiplicativity as a **bundled additive
    homomorphism** from the open-unit-ball multiplicative group `(1+𝔪)` to `(K, +)` — or, at minimum,
    state the standard **multiplicativity lemma** `padicLog p (x*y) = padicLog p x + padicLog p y`
    on `‖·−1‖<1` and the `∀n` power law `padicLog p (x^n) = n • padicLog p x` as the mathlib-facing
    results. The target's `n=p` identity then becomes a one-line specialisation (`map_nsmul`-style),
    not a separately-shipped lemma.
  - Cost: MODERATE (defining the analytic `padicLog` + bundling the hom is real work; the project
    already has the underlying multiplicativity/power-law proofs, so the math is done — it is a
    packaging/upstreaming effort, not new mathematics).
  - Mathlib downstream this enables: the whole `MonoidHom`/`AddMonoidHom` API (`map_one`, `map_mul`,
    `map_pow`, `map_nsmul`, kernels, the log-as-isometry-on-the-exp-ball image lemmas) applies to
    `log_p` for free; every per-exponent power lemma collapses to one structural fact.
  - Real mathematical improvement (not just "looks cooler"): yes — it eliminates the `O(1)`-per-exponent
    lemma proliferation (`padicLog_pow_p`, `padicLog_pow_pPow`, `padicLog_pow`) in favour of one bundled
    homomorphism, which is exactly how mathlib treats `Complex.log`-style and character/valuation maps.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no definitional equalities or typeclass-search paths
introduced). Skipped.

---

### Mathlib search-status: `padicLog_pow_p_of_norm_lt_one` (Phase 5)

[A] Lean-Finder       n/a — no Lean-Finder MCP in this environment; substituted by [D] grep over the
                      vendored mathlib tree (`.lake/packages/mathlib/Mathlib/`, full source) + web
                      lookups against the mathlib4 docs.
[B] Loogle            queried (web): `padicLog`, `p-adic logarithm` → the Loogle/mathlib-docs surface
                      shows **no `padicLog`/`padicExp`** decl. no hits.
[C] LeanSearch        natural-language "p-adic logarithm power law / multiplicative on unit ball"
                      against mathlib4 docs → only `PadicNumbers`, `PadicInt`, `PadicVal` surface; **no
                      analytic log/exp**. no hits.
[D] Grep mathlib src  terms tried: `padicLog`, `padic.?log`, `p.adic.logarithm`, `padicExp`,
                      `p.adic.exponential`, `PowerSeries.log`, `log_pow`, `log_mul`, `FormalGroup`,
                      `logarithm` (under NumberTheory/Padics, Analysis, RingTheory/PowerSeries).
                      Findings:
                        • **No** `padicLog`/`padicExp` (analytic function on `ℚ_p`/extensions) anywhere.
                        • `PowerSeries.log` exists (`RingTheory/PowerSeries/Log.lean`) — the **formal**
                          series `log(1+X)`, with `coeff_log`, `deriv_log`, `logOf_eq`, `map_log`. These
                          are formal-algebra facts; there is **no analytic evaluation, no convergence
                          theory, and no `log_pow`/`log_mul` for a function on a normed field**.
                        • `RingTheory/FormalGroup/Basic.lean` exists (`FormalGroup`, `𝔾ₘ`) — relevant
                          only to the Phase-4c modern-idiom angle, not an existing form of this result.
                      hits: only the **formal** `PowerSeries.log` building block; not the analytic result.
[E] Name pattern      `_pow_p_of_norm_lt_one`, `padicLog_pow` over mathlib → **zero** matches.
                      Within AINTLIB: TWO project-local `padicLog` defs exist —
                      `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:384` (general extension `L`;
                      the one this theorem uses) and
                      `projects/FltRegularBernoulli/BernoulliRegular/FLT37/PadicL/PadicLog.lean:52`
                      (on `ℚ_p` only). Intra-library duplication noted (relevant to the verdict's
                      packaging question; mathlib itself has neither).

Searched for both:
  - the user's current form (`padicLog (z^p) = p • padicLog z` on `‖z−1‖<1`) → not in mathlib.
  - the literature-standard form (multiplicativity `log_p(xy)=log_p x+log_p y` and the `∀n` power law,
    and any analytic `padicLog`/`padicExp` whatsoever) → **not in mathlib in any form**.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib has
the *formal* `PowerSeries.log` building block and `FormalGroup` scaffolding, but **no analytic `p`-adic
logarithm, no multiplicativity/power-law on the open unit ball**.

---

### Call sites — `padicLog_pow_p_of_norm_lt_one` (Phase 6.0)

Internal use count: **1** (within the project, excluding the declaring line). The single real call:

| Caller file:line                  | Usage pattern (one-line excerpt)                                                                 |
|------------------------------------|--------------------------------------------------------------------------------------------------|
| `ValuesAtOne.lean:536`             | `rw [pow_succ, pow_mul, padicLog_pow_p_of_norm_lt_one (p := p) (boundary_norm_pow_sub_one_lt_one hz (p ^ M)), ih, …]` — the successor step of `padicLog_pow_pPow_of_norm_lt_one` (the `p^N` law). |
| `ValuesAtOne.lean:1345` (comment)  | named in a docstring describing the analytic-layer chain (not a call).                            |

External-to-file callers: **0 distinct files** (the only real use is in the same file).

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - (none) — but note the **chain context**: this lemma's *sole* consumer
    `padicLog_pow_pPow_of_norm_lt_one` (the `p^N` law, line 531) is itself consumed by the genuinely
    reused results `padicLog_mul_of_norm_lt_one` (line 543, used in `ResidueZeta.lean:1297, 1575`) and
    `extLog_eq_padicLog_of_norm_lt_one` (line 590, used in `ResidueZeta.lean:1377`,
    `ValuesAtOne.lean:1083`). So the target is a **load-bearing internal scaffold**: K = 1, but the
    chain it feeds is broadly consumed.

Composability signal read: K = 1 internal use (the lemma is a single-purpose stepping-stone toward
the `p^N` law). Per the Phase-6 signal table, K = 1 "possibly the wrong abstraction / could be inlined"
— but here it is genuinely the cleanest decomposition of the `p^N` induction, not an accidental
wrapper. The signal is consistent with "internal scaffold, not a mathlib-facing API surface in its own
right."

### Composition check (Phase 6)

Can `padicLog_pow_p_of_norm_lt_one` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: specialise some mathlib `p`-adic-log power lemma.
  - Mathlib decls used: none exist (Phase 5: mathlib has no analytic `padicLog`).
  - Result: **fails** — there is nothing to specialise.

Attempt 2: build it from `PowerSeries.log` + substitution lemmas.
  - Mathlib decls used: `PowerSeries.log`, `PowerSeries.substAlgHom`, `map_pow`/`map_smul`.
  - Result: **fails** — these are formal-algebra facts. Turning the formal identity
    `φ(log) = p·log` into the analytic statement `padicLog(z^p) = p·padicLog z` on `‖z−1‖<1` requires
    the project's *analytic evaluation bridge* (`seriesEval_formalLog`, `seriesEval_phi_of_summable_prod`,
    `summable_prod_of_norm_coeff_le_linear`) — i.e. summability + `tsum` reindexing over a normed field.
    That is a multi-lemma analytic argument, not a 1–3-call composition. Mathlib lacks the bridge
    entirely.

Conclusion: **NOT-COMPOSABLE** from mathlib. (It *is* a short composition from the **project's own**
analytic-bridge lemmas — but those are not in mathlib, and assembling them is a genuine analytic proof,
not a mathlib-primitive composition.)

---

## Verdict: `padicLog_pow_p_of_norm_lt_one`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): unanimous — `log_p` multiplicativity / power law on the open unit ball
  `‖z−1‖<1` is classical textbook material (Wikipedia, PlanetMath Proposition, MIT 18.785, Koblitz,
  Iwasawa, nLab, recent arXiv). The `n=p` case is one instance of the standard `∀n` law.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** on the exponent axis (`n=p`
  vs the literature `∀n`); base-field and domain axes already maximally general. Phase 4c: a modern
  bundled-homomorphism idiom is available and is a real organisational improvement.
- Mathlib search (Phase 5): **not in mathlib in any form** — mathlib has no analytic `p`-adic
  logarithm at all (only the *formal* `PowerSeries.log`).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (needs the project's analytic
  evaluation bridge, which mathlib lacks). Call sites: K = 1, an internal scaffold feeding a
  broadly-consumed chain.

**Rationale (1–2 paragraphs):**

The mathematical *content* is impeccably mathlib-worthy and entirely missing from mathlib: there is
**no analytic `p`-adic logarithm anywhere in mathlib**, and the multiplicativity / power law on the
open unit ball `‖z−1‖<1` is one of the most standard facts in `p`-adic analysis (it is the very trick
by which Iwasawa extends `log_p` to `|x|=1`). So the high-level answer is clearly "mathlib should have
this material." But this *particular declaration* is the wrong grain to ship: it is the **`n=p`
specialisation** of the standard `∀n` power law (Phase 4b: STRICTLY NARROWER), it has a single internal
call site (it is a scaffold for the `p^N` induction, not a public API surface), and the project itself
already proves both the general `∀n` form (`padicLog_pow_of_norm_lt_one`, line 577) and the more
fundamental multiplicativity (`padicLog_mul_of_norm_lt_one`, line 543) from which everything follows.
The skill's gates forbid `YES-add-as-is` here (Phase 4b is STRICTLY NARROWER, and Phase 4c found a
real modern idiom), and `NO-mathlib-has-it` / `NO-composable-from-mathlib` are both factually false
(mathlib has nothing and the result is not a mathlib-primitive composition).

That leaves `YES-but-generalise-first` vs `BORDERLINE`. The honest reason this is **BORDERLINE rather
than a clean YES-but-generalise-first** is that the real decision is a *packaging/scope* judgment the
skill cannot make alone: (a) the right mathlib contribution is almost certainly **not this lemma nor
even the `∀n` power law in isolation, but the whole `padicLog` package** — define the analytic
`p`-adic log (mathlib has none), prove `padicLog_one`/multiplicativity/power-law on the unit ball, and
ideally bundle it as an `AddMonoidHom` per Phase 4c — a multi-declaration upstreaming project, not a
single-lemma PR; (b) AINTLIB already carries **two** independent `padicLog` definitions
(`PadicExp.lean:384` over a general extension `L`, and `FltRegularBernoulli/.../PadicLog.lean:52` over
`ℚ_p`), so before any mathlib PR the project must decide *which* definition (and at what base-field
generality) is the canonical one to upstream — a cross-project dedup + taste call; (c) whether the
`n=p` scaffold should even be a named lemma in the upstreamed version (vs. inlined into the `p^N`
induction or replaced by `map_nsmul` on a bundled hom) is itself a design choice. None of these are
groundable in the search evidence alone; they are exactly the "project policy + mathematical taste +
right grain" judgments the BORDERLINE bucket exists for.

**Numbered questions (≤5):**

1. Is the intended mathlib contribution the **whole analytic `padicLog` package** (definition +
   `log_one` + multiplicativity + power law on `‖·−1‖<1`, ideally bundled as an `AddMonoidHom`), rather
   than this single `n=p` lemma? If yes, this declaration should be folded into that PR as an
   internal step (likely inlined or replaced by `map_nsmul`), not shipped on its own.
2. Which `padicLog` definition is canonical for upstreaming — the **general-extension** one
   (`PadicExp.lean:384`, over any complete ultrametric `ℚ_p`-algebra field `K`) or the **`ℚ_p`-only**
   one (`FltRegularBernoulli/.../PadicLog.lean:52`)? Mathlib would want the more general form; do you
   want to first consolidate the two AINTLIB definitions into one?
3. For a mathlib PR, do you want the **multiplicativity** `padicLog (x*y) = padicLog x + padicLog y`
   on `‖·−1‖<1` (`padicLog_mul_of_norm_lt_one`) as the headline lemma, with the power law `∀n` and
   this `n=p` case as derived corollaries — i.e. ship the general objects, not the specialisation?
4. Should `padicLog`'s multiplicativity be exposed **structurally** (a bundled `AddMonoidHom` from the
   open-unit-ball unit group `(1+𝔪)ˣ` to `(K,+)`, so power laws become `map_nsmul`/`map_pow`), per the
   Phase-4c modern-idiom analysis? This would make `padicLog_pow_p_of_norm_lt_one` unnecessary as a
   standalone lemma.

**Likely resolution given the answers:**
  - If (1) = yes and (3)/(4) favour the general/bundled form → this declaration is **not** upstreamed
    as-is; it becomes an internal step of a `feat(NumberTheory/Padics): add p-adic logarithm` PR (or
    several), and the standalone mathlib-facing verdict effectively folds into
    `YES-but-generalise-first` aimed at `padicLog_mul_of_norm_lt_one` / a bundled `AddMonoidHom`.
  - If the project chooses to keep `padicLog` project-local (e.g. because the `K`-extension generality
    or the RJW `L_p`-value framing is not what mathlib wants yet) → drop from mathlib consideration; it
    is correct project-internal scaffolding as-is.

**Next action:** user answers the 4 questions above; re-run `/mathlibable` (or, more usefully,
`/mathlibable padicLog_mul_of_norm_lt_one` and the analytic `padicLog` definition) to scope the right
mathlib-facing object. The single most valuable upstreaming target in this chain is the **analytic
`padicLog` definition + its multiplicativity on the open unit ball**, since mathlib has no `p`-adic
logarithm at all — this `n=p` power-law lemma is best treated as an internal step of that effort, not
a standalone PR.

---

## Next step

User answers the 4 numbered questions to fix the mathlib-facing grain (whole-`padicLog`-package vs.
single lemma; which of the two AINTLIB `padicLog` defs is canonical; multiplicativity-as-headline;
bundled-hom idiom). The recommended concrete follow-up is to run the assessment on the **analytic
`padicLog` definition (`PadicExp.lean:384`) and its multiplicativity `padicLog_mul_of_norm_lt_one`**,
which are the genuinely mathlib-missing, broadly-reused objects; this `n=p` power-law theorem is an
internal scaffold that should ride along inside that package (likely inlined or as `map_nsmul`), not be
PR'd on its own.
