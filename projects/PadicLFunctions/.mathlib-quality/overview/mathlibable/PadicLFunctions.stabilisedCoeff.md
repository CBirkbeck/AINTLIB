# `/mathlibable` report — `PadicLFunctions.stabilisedCoeff`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               not re-run (per task instruction — build is stale/slow); **reasoned from source**. The declaration and its full dependency chain (`sigmaP`, `zetaNeg`) were read directly and elaborate consistently with the surrounding sorry-free theorems that consume it.
- decl `PadicLFunctions.stabilisedCoeff`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:357`
- kind:                      `def`
- has sorry:                 no (file `EisensteinFamily.lean` is sorry-free)
- module docstring summary:  The p-adic family of Eisenstein series (RJW §8, arXiv:2309.15692 TeX 2361–2446): the Kubota–Leopoldt pseudo-measure interpolates the constant coefficients of the p-stabilised Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`; `stabilisedCoeff` is the rational coefficient sequence that is the pivot between the p-adic family and the complex q-expansion.

---

### Statement (Phase 1)

`PadicLFunctions.stabilisedCoeff` is **a definition** of the following:

For a prime `p` and weight `k`, it is the rational Fourier-coefficient sequence `n ↦ a_n(k)` of the **p-stabilised Eisenstein series** `E_k^{(p)} = E_k − p^{k−1}E_k(p·)` in RJW's normalisation (arXiv:2309.15692, TeX line 2391):

- constant term `a_0 = (1 − p^{k−1})·ζ(1−k)/2`,
- `n`-th term (`n ≥ 1`) `a_n = σ^{p}_{k−1}(n) = Σ_{0 < d ∣ n,\ p∤d} d^{k−1}`, the **prime-to-`p` divisor power sum**.

The sequence is the *pivot* object: the p-adic side (`eisensteinFamily_interpolation`) proves the moments of the Λ-adic family equal `stabilisedCoeff p k n`, and the complex side (`hasSum_stabilisedEisenstein`, in `EisensteinComplex.lean`) proves the q-series `Σ_n stabilisedCoeff(p,k,n)·qⁿ` sums to the q-expansion of `E_k^{(p)}`. The two halves of the project meet at this definition.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the section's fixed prime (the `if` branch and `sigmaP` both use `p`).
- `k : ℕ` — the weight; the formula uses `k − 1` throughout.

Hypotheses (Lean side):
- none on the def itself.

Conclusion (math): the explicit rational coefficient sequence of `E_k^{(p)}`.

Conclusion (Lean): n/a — definition. Type is `ℕ → ℚ`, body
```lean
fun n => if n = 0 then (1 - (p : ℚ) ^ (k - 1)) * zetaNeg (k - 1) / 2
         else sigmaP p (k - 1) n
```
where `zetaNeg (k-1) : ℚ = (-1)^(k-1)·B_k/k` (project-local, `KubotaLeopoldt/ZetaValues.lean:17`) and `sigmaP p (k-1) n : ℕ = Σ_{0<d∣n, p∤d} d^(k-1)` (project-local, `EisensteinFamily.lean:62`, coerced `ℕ → ℚ`).

---

### Size classification (Phase 2a)

**Verdict: SMALL** (leaning BIG-adjacent)

Reason: It is *not* a new mathematical structure (no topology / category / measurability notion) and not a person/place theorem. It is a **named coefficient sequence for one specific construction** — closer to a helper definition than to a primary structure. It *is* listed implicitly as the bridge object in the module docstring ("the two sides meet in the rational coefficient sequence `stabilisedCoeff`"), which gives it project-architectural significance, but it is not a `## Main results` theorem. Classified SMALL.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: 1 substantive expression — a single `if n = 0 then … else …` (formatted over two physical lines 358–359, but one branching term).

One-liner verdict: **ONE-LINER** (a `def` whose body is one branching expression).

Exemption check:

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|--------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | The body is unfolded freely at every call site via `rw [stabilisedCoeff]` / `simp only [stabilisedCoeff]` (see `EisensteinFamily.lean:395,399`; `EisensteinComplex.lean:237,243,248`). No barrier role. |
| Avoid typeclass diamonds          | no       | Plain `ℕ → ℚ` function; no instance is anchored on it. |
| Mark semantic intent / API name   | **yes**  | This is the *only* reason it exists: it is the shared definitional anchor naming "the coefficients of `E_k^{(p)}`", so the p-adic theorem (`eisensteinFamily_interpolation`, this file) and the complex theorem (`hasSum_stabilisedEisenstein`, `EisensteinComplex.lean`) can both be *stated about the same object*. Without the named sequence, the two independently-developed sides could not be glued by a definitional rewrite. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name).

The exemption is real *within the project* (it is genuine glue between two files), but note it is an **intra-project** API role, not a mathlib-facing one — this is exactly the tension Phase 7 must weigh.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-stabilized Eisenstein series Fourier coefficients formula constant term sigma divisor sum"          | yes  | `E_{k,χ}(z) = L(1−k,χ)/2 + Σ σ_{k−1,χ}(m) qᵐ`; p-stabilisation `E* = E − χ(p)p^{k−1}E(pz)` with coeffs the **prime-to-p** sum `σ^{{p}}_{k−1,χ}(m) = Σ_{d∣m, gcd(d,p)=1} χ(d)d^{k−1}` | Exactly matches `stabilisedCoeff` (trivial χ): constant `(1−p^{k−1})ζ(1−k)/2`, n-th `σ^p_{k−1}(n)`. Sources: Siegel-Eisenstein p-stabilisation papers (arXiv:1207.0198, 2302.13009), Williams arXiv:2309.15692 |
|  2 | WebSearch (general form)         | "Lambda-adic Eisenstein family Fourier coefficients Kubota-Leopoldt p-adic L-function interpolation Ohta" | yes  | The 0-th coefficient of a Λ-adic Eisenstein series is the Kubota–Leopoldt p-adic L-function; higher coeffs interpolate divisor sums | Confirms the *architecture* RJW §8 formalises; this is textbook Hida/Wiles Λ-adic Eisenstein theory |
|  3 | WebSearch (named-after / aliases)| "'prime-to-p' divisor power sum sigma_k coprime restricted divisor function notation arithmetic function" | partial | `σ_k(n) = Σ_{d∣n} d^k` is standard; "restricted divisor function" exists; a *coprime-to-p restricted* `σ` has **no single standard symbol/name** — written ad hoc as `σ^{(p)}`, `σ^{{p}}`, or `Σ_{d∣n,p∤d}` | The prime-to-p restriction is an inline notation, not a named object; varies by author |
|  4 | ChatGPT MCP                      | (configured server `plugin:mathlib-quality:chatgpt-math` present in MCP cache, but **not exposed as a callable tool** in this agent's deferred-tool set; ToolSearch for `chatgpt-math__ask` returned no match) | n/a | — | Channel unavailable in this harness. Compensated by 6 WebSearch/WebFetch queries + nLab + arXiv source fetch (well past the ≥3-distinct-query / multi-generality bar). Recorded honestly as a gap. |
|  5 | Local references                 | `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                    | n/a  | (no references dir; no `refs/` symlink) | Both absent on this checkout (`ls` confirmed). The canonical source is nonetheless identified: **RJW = "An introduction to p-adic L-functions", arXiv:2309.15692**, cited throughout the module by TeX line number ("TeX 2391"). |
|  6 | nLab                             | "p-adic Eisenstein measure family Lambda-adic modular form"                                            | yes  | nLab "p-adic modular form": a limit of modular forms under a topology encoding congruences between Fourier coefficients; p-adic Eisenstein families per Serre/Katz/Ribet | Confirms the family-level concept is standard; nLab has **no** entry for "the stabilised coefficient sequence" as a named object |
|  7 | nCatLab (categorical)            | (same nLab query; checked for a categorical/universal-property framing)                                | no   | — | Not a categorical concept; it is a concrete `ℕ → ℚ` sequence. n/a for a higher-categorical restatement. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | — | Not an algebraic-geometry / scheme-theoretic concept (it is a Fourier-coefficient sequence of a modular form). Recorded n/a after a brief look. |
|  9 | MathOverflow / Math.StackExchange| "p-stabilization Eisenstein series q-expansion coefficients prime to p"                                | yes (via arXiv) | Same shape: divisors `d∣n` with `gcd(d,p)=1` give p-adically convergent `d^{2k−1}`, divisors with `p∣d` drop p-adically; explicit Fourier coeffs of p-stabilised Eisenstein series | MO-style results all reduce to the standard formula; no separate "named coefficient sequence" emerges |
| 10 | recent arXiv (last 5 years)      | fetched arXiv:2309.15692 (RJW, the project's own source) for the verbatim formula; also surfaced 1207.0198/2302.13009 (2012/2023), 2505.06956 (2025) | partial | The fetched RJW PDF was binary/compressed and the small-model extractor could not read the formula text; **the formula is independently confirmed by channels #1, #2, #9** | Direct quote from RJW unavailable due to PDF encoding; the coefficient shape is corroborated across ≥3 other channels |

The protocol passed: WebSearch ran 3 distinct queries at three generality levels (specific p-stabilisation form; general Λ-adic-family / Kubota–Leopoldt level; named-after / restricted-σ aliases); local refs checked (absent, source identified); nLab checked; nCatLab / Stacks / MathOverflow / arXiv each checked or recorded n/a with reason. The only true gap is the ChatGPT MCP channel, which is not callable in this harness — recorded honestly and over-compensated by the source-fetch + extra web queries.

### Literature summary (Phase 3)

Concept identified as: **the Fourier (q-expansion) coefficient sequence of the p-stabilised level-1 Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`** (trivial-character case of the classical p-stabilisation). Its two ingredients have standard names — the **value `ζ(1−k)`** (= `(-1)^{k-1}B_k/k`, classical) and the **prime-to-p restricted divisor power sum** `σ^p_{k−1}(n)` (standard *operation*, ad-hoc notation). The packaged sequence itself is **not a named standalone object** in the literature.

Sources agree on the standard form: **yes** — constant term `(1−p^{k−1})ζ(1−k)/2`, n-th term `σ^p_{k−1}(n)`. This is uniform across the Siegel-Eisenstein p-stabilisation literature, the Hida/Wiles Λ-adic-Eisenstein architecture, and RJW arXiv:2309.15692 §8 (the project's source).

Most general standard form: the coefficient sequence of a p-stabilisation of a (possibly nebentypus-`χ`, possibly higher-level) Eisenstein series; the trivial-character / level-1 case is the one formalised here.

Generality dimensions where the literature varies:
- **Character**: trivial χ (here) → arbitrary Dirichlet character χ (general: `σ_{k−1,χ}` with `χ(d)` weights, constant term `L(1−k,χ)/2`). The general form is strictly broader.
- **Prime-to-p restriction symbol**: no canonical name (`σ^{(p)}`, `σ^{{p}}`, inline `Σ_{d∣n,p∤d}`).
- **Codomain / packaging**: literature treats it as the q-expansion of a *modular form*, not as a free-standing `ℕ → ℚ` indexed sequence.

Disagreement with the literature: **none on the formula** — `stabilisedCoeff` is exactly the trivial-character, level-1 specialisation of the standard p-stabilised Eisenstein coefficients. The divergence is *organisational*: the literature does not reify "the coefficient sequence" as a named object; it reads coefficients off the modular form.

---

### Generality analysis — `PadicLFunctions.stabilisedCoeff`

Literature-standard form (from Phase 3): coefficients of `E_{k,χ}^{(p)}` — constant `L(1−k,χ)/2`, n-th `σ^{p}_{k−1,χ}(n) = Σ_{d∣n, p∤d} χ(d)d^{k−1}`, for an arbitrary Dirichlet character χ (and, more generally, arbitrary level).

| # | Parameter / hypothesis        | Current Lean form                  | Literature-standard form                  | Weaker/more-general form exists? | Reason it can/can't be generalised |
|---|-------------------------------|------------------------------------|--------------------------------------------|----------------------------------|-------------------------------------|
| 1 | character                     | trivial (no χ)                     | arbitrary Dirichlet character χ            | **yes**                          | Standard p-stabilisation is stated with χ; the trivial-χ case here is a genuine specialisation. Generalising would mean `σ^p_{k−1,χ}` (χ-weighted) and constant `L(1−k,χ)/2`. |
| 2 | level                         | level 1 (`SL₂(ℤ)`)                 | arbitrary level / Eisenstein at a cusp     | yes                              | Broader theory exists; far outside this project's scope. |
| 3 | weight index `k`              | `k : ℕ`, uses `k−1`               | same                                       | NO                               | Already the natural index. The `k−1`/`Nat`-subtraction shape is project bookkeeping, not a generality axis. |
| 4 | codomain                      | `ℕ → ℚ` (rational coeffs)          | coefficients of a modular form (q-expansion) | n/a (different organisation)     | This is the modernisation question, handled in 4c — mathlib would not store this as a standalone `ℕ → ℚ`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along the character/level axes (trivial χ, level 1), but this narrowing is *deliberate and project-appropriate*: RJW §8 itself works the trivial-character level-1 case as "the simplest example of p-adic variation". The narrowing is not an oversight to be mechanically widened — it is the chosen object of study.

Number of meaningful generalisation opportunities found: 2 (character, level), both **EXPENSIVE** and **out of the formalised project's intent**.

Proposed restatement (if pursued): a χ-indexed coefficient sequence built on a χ-weighted prime-to-p divisor sum and a Dirichlet `L(1−k,χ)` value. Cost: **EXPENSIVE** — would require χ-weighted `sigmaP`, a Dirichlet-L analog of `zetaNeg`, and re-proving both the p-adic interpolation and the complex q-expansion identities for general χ. None of that machinery exists in the project.

Note per the skill: EXPENSIVE does not by itself downgrade a verdict — but here the generalisation is also (a) not what mathlib would store (see 4c) and (b) a scope question, which pushes toward BORDERLINE rather than a clean YES-but-generalise-first.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question                                                                                                   | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|---------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances?                                                        | no       | Already just `p` + `Fact p.Prime` + `k`; nothing to bundle.                            | — |
|  2 | sequences/metric → filters/topological?                                                                    | no       | It is an algebraic coefficient sequence; no limit/convergence notion to filter-ise.    | — |
|  3 | **construct an object where a universal-property / canonical-construction class would characterise it?**   | **yes**  | In mathlib idiom, the coefficients of `E_k^{(p)}` would be **read off via `UpperHalfPlane.qExpansion (E_k − p^{k−1}·E_k(p·))`** (`Mathlib/NumberTheory/ModularForms/QExpansion.lean`, def `qExpansion` + `qExpansion_coeff`), *not* predefined as a standalone `ℕ → ℚ` literal. The modular-form-first organisation is mathlib's existing pattern (cf. `discriminant_qExpansion_coeff_one`). | Auto-connects to all `qExpansion` API, `ModularForm` Hecke theory, and the `EisensteinSeries` q-expansion development already in mathlib. |
|  4 | set-with-closure-predicate → bundled substructure?                                                          | no       | n/a — it is a function, not a set. |
|  5 | vector-space/metric/field-specific → weaken typeclass?                                                      | no       | Codomain `ℚ` is already the natural base; the relevant generality axis is the *character*, not a typeclass. |
|  6 | 1-categorical → higher-categorical?                                                                         | no       | n/a. |
|  7 | **concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid?**                                                       | partial  | Index is `ℕ` (Fourier index) — intrinsically ℕ; not a generalisation axis. The *real* generalisation is the χ-character one (Phase 4a #1), not the index. | — |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes
  - Proposed mathlib-idiomatic restatement: do NOT define a standalone `stabilisedCoeff : ℕ → ℚ`.
    Define the p-stabilised Eisenstein modular form, then obtain its coefficients via
    `qExpansion`/`qExpansion_coeff` (and, for the prime-to-p divisor part, a χ-weighted /
    prime-to-p variant of `ArithmeticFunction.sigma`).
  - Cost: EXPENSIVE (requires a `ModularForm`-level construction of `E_k^{(p)}` and the
    q-expansion identification — the project currently obtains this only as a `HasSum` statement,
    `hasSum_stabilisedEisenstein`, not as a `ModularForm`/`qExpansion` object).
  - Mathlib downstream this enables: integration with `UpperHalfPlane.qExpansion`,
    `ModularForm` Hecke operators, and the existing `EisensteinSeries.QExpansion` API.
  - Real mathematical improvement (not just "looks cooler"): yes — a standalone hand-rolled
    `ℕ → ℚ` coefficient literal duplicates information that mathlib reads off a modular form;
    the modernisation removes that redundancy and plugs into existing q-expansion machinery.
```

The modern-idiom finding is significant: it means a YES-add-as-is on the *current* `ℕ → ℚ` shape would be wrong, and even a literature-generalised χ-version would still want to be the q-expansion of a modular form rather than a free-standing sequence. This is decisive against any straight YES and is one of the inputs that makes the verdict a judgment call.

---

### Diamond / defeq risk — `PadicLFunctions.stabilisedCoeff`

| # | Risk                          | Verdict | Evidence / rationale                                                                                             |
|---|-------------------------------|---------|------------------------------------------------------------------------------------------------------------------|
| 1 | Typeclass diamond             | none    | Plain function `ℕ → ℚ`; introduces no instance. The only typeclass in scope (`Fact p.Prime`) is a parameter, not produced. |
| 2 | Reducibility leak             | none    | Not `@[reducible]`. Body is a small `if`; even if exposed, `if n = 0 then … else …` defeq-checking is cheap and predictable. |
| 3 | Non-canonical unfolding       | low     | Every call site already unfolds it deliberately (`rw [stabilisedCoeff]`, `simp only [stabilisedCoeff]`). Behaviour is exactly what authors expect; no surprise unfolding. |
| 4 | Instance priority collision   | none    | Not an instance. n/a. |
| 5 | Universe-polymorphism issues  | none    | Monomorphic: `ℕ → ℚ`. No universe variables. |
| 6 | Coercion ambiguity            | none    | No `CoeFun`/`CoeSort`. (The `ℕ → ℚ` coercion on `sigmaP`'s `ℕ` result is mathlib's standard `Nat.cast`; no competition.) |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**
Top risks: none
Recommended mitigations: n/a

(The def is infrastructurally harmless. Risk is not the reason this is not a YES; the reasons are organisational/scope — Phases 4c, 6, 7.)

---

### Mathlib search-status: `PadicLFunctions.stabilisedCoeff`

[A] Lean-Finder       (tool not available in harness)                              n/a: Lean-Finder MCP not exposed here
[B] Loogle            (tool not available in harness; emulated by typed grep below) n/a: replaced by [D] typed source grep over mathlib
[C] LeanSearch        (tool not available in harness; emulated by WebSearch #1–#3)  n/a: NL search done via web channels in Phase 3
[D] Grep mathlib src  `stabilis|stabiliz`, `pStabilis|p_stabilis`, `stabilisedEisenstein|stabilizedEisenstein`, `Eisenstein` (file list), `qExpansion`, `sigma`/`ArithmeticFunction.sigma`, `riemannZeta_neg_nat`, `sigma.*coprime|divisors.*filter.*coprime`   no hits for the object; building blocks found (see below)
[E] Name pattern      `stabilisedCoeff` qualified over `Mathlib/`                   no hits

Searched for both:
  - the user's current form (`stabilisedCoeff`, a standalone `ℕ → ℚ` p-stabilised-Eisenstein coefficient sequence) — **not in mathlib** (zero hits, all methods).
  - the literature-standard form (p-stabilised Eisenstein q-expansion coefficients; prime-to-p divisor sum) — **the packaged object is not in mathlib**; only the *building blocks* are:
    - `ArithmeticFunction.sigma k` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143`, notation `σ`) — the *full* divisor power sum `σ_k(n) = Σ_{d∣n} d^k`. Mathlib has **no prime-to-p / coprime-restricted** variant (`sigmaP` is project-local; the project bridges them via `sigmaP_eq_of_not_dvd` and `sigmaP_add_pow_mul_sigma_div` in `EisensteinComplex.lean`).
    - `riemannZeta_neg_nat_eq_bernoulli` (`Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:27`) — `riemannZeta (-k) = (-1)^k·bernoulli(k+1)/(k+1)`, i.e. the *complex* value of what `zetaNeg` packages rationally. The project's `zetaNeg : ℕ → ℚ` is its own rational object (bridged to this in `ZetaValuesComplex.lean`).
    - `UpperHalfPlane.qExpansion` / `qExpansion_coeff` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:166,169`) — the generic way mathlib reads Fourier coefficients off a modular form.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). Mathlib has the *ingredients* (`σ`, `riemannZeta_neg_nat_eq_bernoulli`, `qExpansion`) but neither the prime-to-p restricted `σ`, nor the rational `ζ(1−k)` object `zetaNeg`, nor the packaged `stabilisedCoeff` sequence.

---

### Call sites — `PadicLFunctions.stabilisedCoeff`

Internal use count: **K = 1 external file** (within the project, NOT counting the declaring file's own theorem). The declaring file itself also uses it (in `eisensteinFamily_interpolation`).

External-to-file callers: 1 distinct file (`EisensteinComplex.lean`).

| Caller file:line                                   | Usage pattern (one-line excerpt)                                                              |
|----------------------------------------------------|-----------------------------------------------------------------------------------------------|
| `EisensteinFamily.lean:385` (declaring file)       | `… = ((b:ℚ_[p])^k − 1) * ((stabilisedCoeff p k 0 : ℚ) : ℚ_[p]))` — p-adic side, constant term |
| `EisensteinFamily.lean:391,395,399` (declaring file)| `… = ((stabilisedCoeff p k n : ℚ) : ℚ_[p])`; then unfolded `rw [stabilisedCoeff, if_pos/if_neg …]` — p-adic interpolation |
| `EisensteinComplex.lean:190`                       | `(fun n => ((stabilisedCoeff p k n : ℚ) : ℂ) * exp(2πiz)^n)` — complex side `HasSum` statement |
| `EisensteinComplex.lean:231,237,243,248`           | `(fun n => ((stabilisedCoeff p k n : ℚ) : ℂ) * qⁿ) = …`; then `simp only [stabilisedCoeff, …]` to split into branches | 

Inline-derivation grep (was the equivalent re-derived elsewhere without using `stabilisedCoeff`?):
  - (none) — the sequence is referenced by name in both halves; not re-spelled inline anywhere.

What the pattern tells us: this is the **architectural pivot** of the project. K=1 external file is low on raw count, but the use is load-bearing in a way the count understates: the p-adic theorem (`eisensteinFamily_interpolation`) and the complex theorem (`hasSum_stabilisedEisenstein`) are *both stated about this same object*, which is the whole point of defining it (the docstring says so: "the two sides meet in `stabilisedCoeff`"). This is the Phase-2b "semantic intent / API name" exemption made concrete — but it is an **intra-project** glue role, not evidence of mathlib-facing demand.

---

### Composition check (Phase 6)

Can `stabilisedCoeff` be derived from mathlib in ≤3 chained calls?

Attempt 1: `fun n => if n = 0 then (1 - (p:ℚ)^(k-1)) * (rational ζ(1−k)) / 2 else (σ^p_{k−1}(n) : ℚ)`
  - Mathlib decls available: `ArithmeticFunction.sigma`, `riemannZeta_neg_nat_eq_bernoulli`.
  - Result: **fails** — two of the three needed ingredients are not in mathlib:
    1. the **prime-to-p restricted** `σ` (mathlib has only full `σ`; the restriction `Σ_{d∣n,p∤d}` is `sigmaP`, project-local — building it from `σ` is itself a multi-step development, cf. the project's own `sigmaP_add_pow_mul_sigma_div`),
    2. the **rational** value `ζ(1−k) = (-1)^{k-1}B_k/k` as a `ℚ` (mathlib's `riemannZeta_neg_nat_eq_bernoulli` is a *complex* identity; `zetaNeg : ℕ → ℚ` is project-local, defined directly from `bernoulli`).
  - Notes: even the rational `ζ(1−k)` is arguably a `≤1`-line composition `(-1)^k * bernoulli (k+1) / (k+1)` of `Mathlib.bernoulli` — but the prime-to-p `σ` is not, and bundling the whole `if`-sequence is a 3rd layer.

Attempt 2: read coefficients off `qExpansion (E_k^{(p)})`.
  - Mathlib decls: `UpperHalfPlane.qExpansion`, `qExpansion_coeff`, `EisensteinSeries` API.
  - Result: **fails as a composition** — requires first *constructing* `E_k^{(p)}` as a mathlib `ModularForm` and proving its q-expansion equals this formula. That is exactly the EXPENSIVE modern-idiom development of Phase 4c, not a ≤3-call inline.

Conclusion: **NOT-COMPOSABLE** (no ≤3-mathlib-call inline; the two essential ingredients `sigmaP` and `zetaNeg` are themselves project-local and not in mathlib).

---

## Verdict: `PadicLFunctions.stabilisedCoeff`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *formula* is standard (trivial-χ, level-1 p-stabilised Eisenstein coefficients: constant `(1−p^{k−1})ζ(1−k)/2`, n-th prime-to-p divisor sum `σ^p_{k−1}(n)`), confirmed across ≥4 channels — **but the packaged "coefficient sequence" is not a named standalone object**; the literature reads coefficients off a modular form.
- Generality analysis (Phase 4): **STRICTLY NARROWER** than the χ-general literature form (trivial character, level 1); generalisation is EXPENSIVE and out of the project's intent. Phase 4c found a real modern-idiom improvement: store it as `qExpansion` of a `ModularForm`, not as a free-standing `ℕ → ℚ`.
- Diamond/defeq risk (Phase 4.5): NONE.
- Mathlib search (Phase 5): **not in mathlib**; only the building blocks (`ArithmeticFunction.sigma`, `riemannZeta_neg_nat_eq_bernoulli`, `qExpansion`) — crucially **no prime-to-p `σ`** and **no rational `zetaNeg`**.
- Composition check (Phase 6): **NOT-COMPOSABLE** (two essential ingredients are project-local, not mathlib; a clean derivation needs the EXPENSIVE modular-form construction).
- Call sites (Phase 6.0): K = 1 external file, but a load-bearing architectural pivot between the project's p-adic and complex halves (Phase-2b semantic-intent exemption applies — *intra-project*).

**Rationale:**

`stabilisedCoeff` sits exactly on the line the BORDERLINE bucket exists for. Three findings independently rule out a clean YES, and a fourth independently rules out a clean NO. (1) **Not YES-add-as-is**: it is strictly narrower than the literature standard (trivial character, level 1), so the YES-as-is gate is failed by Phase 4b — and Phase 4c found that even the right *general* form would not be a standalone `ℕ → ℚ` literal but the `qExpansion` of a modular form, so the current shape is not mathlib-idiomatic regardless of generality. (2) **Not YES-but-generalise-first in any actionable sense**: the only generalisations the literature offers (character, level) are EXPENSIVE *and* would still be subsumed by the modular-form-first organisation; "generalise this `ℕ → ℚ` literal" is not the right move — the right move is "build the modular form and read its q-expansion", which is a different, large piece of work. (3) **Not NO-mathlib-has-it / NO-composable**: mathlib has neither the object nor a ≤3-call inline for it; its two essential ingredients (`sigmaP`, the prime-to-p divisor sum; `zetaNeg`, the rational `ζ(1−k)`) are themselves project-local and absent from mathlib, and assembling it via `qExpansion` requires constructing `E_k^{(p)}` as a `ModularForm` first. So Phase 6 is genuinely NOT-COMPOSABLE — yet that non-composability is *because of missing upstream pieces*, not because the object is deep.

What remains is a pure judgment call about **mathlib scope and the upstreaming order**, which the skill cannot settle alone — and which is *consistent with the sibling assessments in this same batch*: the two definitions `stabilisedCoeff` is built on, `PadicLFunctions.sigmaP` and `PadicLFunctions.divisorMeasure`, were both independently assessed `BORDERLINE-needs-human`. `stabilisedCoeff` is the rational-coefficient pivot of that same RJW-bookkeeping cluster: it is named with project-internal terminology ("stabilised", anchored to "RJW TeX 2391"), it exists chiefly as glue between two files, and whether the underlying *p-stabilised-Eisenstein coefficient* concept belongs in mathlib depends on decisions about its dependencies (`sigmaP`, `zetaNeg`) and its preferred organisation (sequence vs. modular-form q-expansion) that only the maintainer can make.

**Numbered questions (≤5):**

1. Is `stabilisedCoeff` intended to be a public-facing object for downstream developments, or is it purely internal glue tying *this* project's p-adic side (`eisensteinFamily_interpolation`) to its complex side (`hasSum_stabilisedEisenstein`)? (If purely internal: drop from mathlib consideration; keep project-local.)

2. The two ingredients it is built on — `sigmaP` (prime-to-p divisor power sum) and `zetaNeg` (rational `ζ(1−k)`) — are both BORDERLINE for mathlib themselves. Do you want to upstream *those* first? Mathlib has full `ArithmeticFunction.sigma` but no prime-to-p variant, and `riemannZeta_neg_nat_eq_bernoulli` but no standalone rational `zetaNeg`. `stabilisedCoeff` cannot sensibly go to mathlib before they do.

3. If this concept were to go to mathlib, would you accept the **modern-idiom** form (Phase 4c) — define `E_k^{(p)}` as a `ModularForm` and obtain its coefficients via `UpperHalfPlane.qExpansion` — rather than a standalone `ℕ → ℚ` literal? That is the mathlib-idiomatic organisation but is an EXPENSIVE re-development (the project currently only has the `HasSum`, not a `ModularForm`/`qExpansion` object).

4. Is the **trivial-character, level-1** specialisation acceptable as a mathlib contribution, or would mathlib want the **χ-general** p-stabilised Eisenstein coefficients (the standard literature form)? The general form is EXPENSIVE here (needs χ-weighted `sigmaP` and a Dirichlet-`L(1−k,χ)` value object, neither of which the project has).

**Next action:** user answers the questions; re-run `/mathlibable PadicLFunctions.stabilisedCoeff` to resolve. Likely outcomes:
  - Internal glue only → drop from mathlib consideration entirely; keep project-local (matches the `sigmaP` / `divisorMeasure` BORDERLINE outcomes).
  - Public + willing to upstream the modular-form-first form → re-aim at a `qExpansion`-based contribution (after `sigmaP`/`zetaNeg` land); likely `YES-but-generalise-first` with reason MODERN-IDIOM.
  - Public but unwilling to do the EXPENSIVE `ModularForm` redevelopment → still BORDERLINE (a cost-vs-scope call the maintainer owns).

---

## Next step

User answers the four questions above; re-run `/mathlibable PadicLFunctions.stabilisedCoeff` to resolve. The most likely resolution, consistent with the BORDERLINE verdicts already recorded for its dependencies `sigmaP` and `divisorMeasure`, is to keep `stabilisedCoeff` project-local (it is internal glue between the project's p-adic and complex sides, depends on two not-yet-upstreamed helpers, and would need an EXPENSIVE modular-form-first redevelopment to be mathlib-idiomatic).
