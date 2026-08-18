# `/mathlibable` report — `PadicLFunctions.eisensteinFamily`

**Final verdict: `BORDERLINE-needs-human`.**

> The *mathematical object* — the Λ-adic (Serre / Wiles / Katz) family of p-stabilised
> Eisenstein series `𝐄 = Σ_{n≥0} A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`, with constant coefficient
> `A₀ = x·ζ_p/2` (a twist of the Kubota–Leopoldt p-adic zeta) and non-constant coefficients
> the divisor-sum measures `A_n = Σ_{0<d∣n, p∤d} δ_d` — is **canonical and central** to the
> whole subject (this is exactly the bootstrap by which the p-adic zeta is the constant term
> of a p-adic Eisenstein family). Mathlib has **none** of it, and it is **not composable**
> from mathlib primitives — because the entire substrate is absent (no p-adic measure type,
> no Iwasawa algebra `Λ(ℤ_p^×)`, no total fraction ring `Q(ℤ_p^×)`, no pseudo-measure
> formalism, no Kubota–Leopoldt p-adic zeta `padicZeta`, no x-twist). The honest blockers are
> not search blockers but *roadmap / policy* ones: this terminal `def` cannot be upstreamed in
> isolation (it is the keystone of a large project-local tower whose own foundation pieces were
> all assessed BORDERLINE/NO), it has **0 consumers outside its own file**, and which object is
> the real mathlib target — the *family* `eisensteinFamily`, the *interpolation theorem*
> `eisensteinFamily_interpolation`, or `padicZeta` itself — plus the `½`/`p ≠ 2` encoding, are
> judgments the skill cannot ground in evidence alone. Numbered questions in Phase 7.

---

## Phase 0 — Baseline / doctor

- **Target:** `PadicLFunctions.eisensteinFamily`, kind `def` (`noncomputable def`),
  at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:364`.
- **lake build:** *build not re-run; reasoned from source* (per the task's Phase-0 fallback —
  `lake build` is stale/slow in this checkout). The declaration and its full dependency chain
  (`twistedZetaHalf`, `divisorMeasure`, `quotientTwist`, `unitsTwist`, `padicZeta`,
  `QuotientField`, `PadicMeasure`, `PowerSeries.mk`) were read directly from source.
- **decl resolved:** ✓ at `EisensteinFamily.lean:364`.
- **has sorry:** **no** — `grep` for `sorry`/`admit` over `EisensteinFamily.lean` returns
  nothing; the declaration and every dependency are complete (this is fleet-eligible work).
- **module docstring summary:** the Part-I closer — the Kubota–Leopoldt pseudo-measure
  interpolates the constant coefficients of the p-stabilised Eisenstein series `E_k^{(p)}`,
  the non-constant coefficients are divisor-sums of Diracs, and bundling coefficientwise gives
  the Λ-adic Eisenstein family `𝐄` (RJW Theorem at TeX 2399).

```lean
/-- R8 (RJW TeX 2399–2400): the Λ-adic Eisenstein family
`𝐄 = Σ_{n≥0} A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`: constant coefficient `A₀ = x·ζ_p/2`,
higher coefficients the divisor-sum measures `A_n`. -/
noncomputable def eisensteinFamily (hp2 : p ≠ 2) :
    PowerSeries (PadicMeasure.QuotientField p) :=
  PowerSeries.mk fun n =>
    if n = 0 then twistedZetaHalf p hp2
    else algebraMap _ _ (divisorMeasure p n)
```

## Phase 1 — Comprehend

### Statement (Phase 1)

`eisensteinFamily p hp2` is **a definition** of the following object.

Let `p` be an odd prime. Working in the total ring of fractions `Q(ℤ_p^×) = Frac(Λ(ℤ_p^×))` of
the Iwasawa algebra (= the `ℤ_[p]`-measures on `ℤ_p^×`), `eisensteinFamily` is the formal power
series in `q` whose coefficient sequence `n ↦ A_n` is

```
A₀ = x·ζ_p/2          (twistedZetaHalf — the x-twist of the Kubota–Leopoldt p-adic
                       zeta pseudo-measure, halved; lives in Q(ℤ_p^×))
A_n = Σ_{0<d∣n, p∤d} δ_d   for n ≥ 1   (divisorMeasure — a measure in Λ(ℤ_p^×), embedded
                                        into Q(ℤ_p^×) by algebraMap)
```

This is the **Λ-adic family of (p-stabilised) Eisenstein series** `𝐄 = Σ_{n≥0} A_n qⁿ`. Its
reason for existing is the coefficientwise *interpolation* property (the immediately following
theorem `eisensteinFamily_interpolation`, and the complex identification
`hasSum_stabilisedEisenstein` in `EisensteinComplex.lean`):

```
∫_{ℤ_p^×} x^{k−1} · 𝐄  =  E_k^{(p)}        for even k ≥ 4,
```

i.e. applying the `(k−1)`-th moment functional to each coefficient recovers the q-expansion of
the p-stabilised classical Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`, whose
coefficient sequence is `stabilisedCoeff p k` (constant term `(1−p^{k−1})ζ(1−k)/2`, `n`-th term
`σ^p_{k−1}(n)`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (section variables).
- `hp2 : p ≠ 2` — oddness, forced by the `½` in `A₀` (`2` is a unit of `ℤ_[p]` iff `p` is odd).

Hypotheses (Lean side): `hp2 : p ≠ 2` (only).

Conclusion (math): the generating power series of the Λ-adic Eisenstein family, with its zeroth
coefficient the twisted half-zeta and higher coefficients the prime-to-`p` divisor-sum Dirac
measures.

Conclusion (Lean): `PowerSeries (PadicMeasure.QuotientField p)` (n/a — this is a definition, so
the "conclusion" is the *type of the defined object*, a power series over `Q(ℤ_p^×)`).

### Dependency tower (all project-local, all sorry-free)

| Symbol | Where | What it is | In mathlib? |
|---|---|---|---|
| `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` | `Measure/Basic.lean:52` | p-adic measures = `ℤ_[p]`-linear functionals on `C(X,ℤ_[p])` (RJW Def 3.6) | **No** |
| `PadicMeasure.QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` | `Measure/PseudoMeasure.lean:804` | total fraction ring `Q(ℤ_p^×)` of `Λ(ℤ_p^×)` (RJW Def 3.34) | **No** |
| `twistedZetaHalf p hp2` | `EisensteinFamily.lean:186` | `A₀ = x·ζ_p/2` (this file's n=0 coeff) | **No** (assessed BORDERLINE) |
| `divisorMeasure p n` | `EisensteinFamily.lean:68` | `A_n = Σ_{0<d∣n,p∤d} δ_d` (this file's n≥1 coeff) | **No** (assessed BORDERLINE) |
| `quotientTwist` / `unitsTwist` | `EisensteinFamily.lean:167/115` | x-twist `[g]↦g·[g]` on `Q` / `Λ` | **No** (`quotientTwist` NO-mathlib-has-it via `IsLocalization.ringEquivOfRingEquiv`; `unitsTwist` BORDERLINE) |
| `padicZeta p hp2` | `KubotaLeopoldt/ZetaP.lean` | Kubota–Leopoldt p-adic zeta pseudo-measure (RJW Def 4.10) | **No** |
| `PowerSeries.mk` | `Mathlib/RingTheory/PowerSeries/Basic.lean:109` | generic `(ℕ → R) → R⟦X⟧` | **Yes** (generic infra) |

`eisensteinFamily` is the **bundling** of the two coefficient families into a `PowerSeries`. The
*only* mathlib ingredient is the generic `PowerSeries.mk`; every mathematically substantive piece
is project-local and absent from mathlib.

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: BIG.** This is the **main result object** of the file: the module docstring's headline
is "Bundling coefficientwise gives the Λ-adic Eisenstein family `𝐄 = Σ A_n qⁿ` (RJW Theorem at
TeX 2399)", and the very next declaration is the named §8 theorem `eisensteinFamily_interpolation`
about it. It is a named mathematical object of the subject (the Serre/Wiles/Katz Λ-adic Eisenstein
family) — a structure-introducing `def`, not a helper. (Literature width is EXHAUSTIVE regardless;
BIG is recorded for framing.)

### One-line check (Phase 2b)

**Body line count:** 3 substantive lines (`PowerSeries.mk fun n =>` + the two `if`-branches). Kind
is `def`.

**One-liner verdict: MULTI-LINE.** The body is a two-branch data construction
(`PowerSeries.mk` of a piecewise coefficient function), not a single substantive line aliasing a
mathlib decl. The Phase-2b one-liner exemption table is therefore **n/a** (not a one-liner). For
completeness: there is no defeq-abuse / typeclass-diamond concern (no instance, no competing
mathlib definitional path — see Phase 4.5), and the API-name role is real (the interpolation
theorem and `constantCoeff`/`coeff` rewrites are stated against the name).

## Phase 3 — Literature search (EXHAUSTIVE, 9-channel protocol)

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Lambda-adic Eisenstein family power series Iwasawa algebra divisor sum coefficients p-adic zeta constant term" | **yes** | `E*₂ₖ = (1−p^{2k−1})ζ(1−2k)/2 + Σ σ*₂ₖ₋₁(n)qⁿ`; "the p-adic zeta function is the constant term in the q-expansion of a p-adic family of Eisenstein series whose non-constant Fourier coefficients are divisor-sum functions"; Iwasawa algebra `Λ = ℤ_p[[T]] ≅ ℤ_p[[Γ]]`; "formalized by Wiles as the standard example of a Λ-adic family of Eisenstein series." | **Near-exact match** to `stabilisedCoeff` and the family shape. |
| 2 | WebSearch (general / interpolation form) | "p-adic family of Eisenstein series q-expansion coefficients measures interpolation Kubota-Leopoldt Serre" | **yes** | "Serre's approach … uses the whole Eisenstein family for bootstrapping analytic properties from the non-constant terms to the constant term"; `E*₂ₖ = (1−p^{2k−1})ζ(1−2k)/2 + Σ σ*₂ₖ₋₁(n)qⁿ`; Serre's theorem `ζ*(s,u) = L_p(s, ω^{1−u})`. | Confirms the constant-term/p-adic-zeta bootstrap = the object's purpose. |
| 3 | WebSearch (named-after / aliases: Wiles / Hida / Eisenstein measure) | "Wiles Lambda-adic Eisenstein series Hida family Eisenstein measure generating power series ordinary p-adic L-function" | **yes** | "Wiles … realize the Deligne–Ribet p-adic L-function as constant terms of a particular Hida family of Eisenstein series"; "p-adic families of Eisenstein series … constructions completed by Deligne, Katz, Ribet and Serre"; "ordinary Λ-adic modular forms" (Hida). | Names vary widely: *Serre p-adic Eisenstein family*, *Λ-adic Eisenstein family* (Wiles), *Eisenstein measure* (Katz/Eischen), *Hida family of Eisenstein series*. **No single universal name** for the generating power-series object. |
| 4 | ChatGPT MCP (historical-formulation Q) | — | **n/a** | — | No ChatGPT MCP configured this session (no `.mathlib-quality/references/`, no `refs/` symlink). The historical/standard-form question is covered by channels 1–3 (Serre 1973 → Wiles → Hida/Katz lineage). Consistent with all sibling reports in this batch. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/` | **n/a** | (no references dir; no `refs/` symlink) | Directory absent — recorded `n/a`. The source is RJW arXiv:2309.15692 §8 (TeX 2361–2446), cited throughout the file. |
| 6 | nLab | "Eisenstein series" (WebFetch ncatlab.org/nlab/show/Eisenstein+series) | **no** | — | "No mention of p-adic or Lambda-adic Eisenstein families." nLab's page is purely classical complex Eisenstein series; no measure-valued / Iwasawa-algebra coefficients, no named generating-series object. |
| 7 | nCatLab (categorical angle) | (covered by 6) | **n/a** | — | Not a categorical concept; the family is an arithmetic/analytic object. nLab page (channel 6) is the relevant one and has nothing p-adic. |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry topic; Stacks has no p-adic-L / Iwasawa / modular-forms content. |
| 9 | MathOverflow / Math.StackExchange / arXiv | arXiv 2309.15692, 1204.3878, 2101.01879, Marks "p-adic MFs à la Serre", Dasgupta "evil Eisenstein", Hsieh OEPL, CUNY "Hida families" surfaced repeatedly | **yes (concept)** | The constant term of the (Hida/Λ-adic) Eisenstein family = the p-adic L-function; the family is the standard *bootstrap tool*. | All sources treat the family **as a tool / step in a construction**, not as a standalone uniformly-named `def`. RJW arXiv:2309.15692 §8 is the project's exact source. |

### Literature summary (Phase 3)

- **Concept identified as:** the **p-adic (Λ-adic) family of Eisenstein series** — Serre's
  bootstrap object; Wiles's "standard example of a Λ-adic family"; the Katz/Eischen "Eisenstein
  measure"; the Hida-family-of-Eisenstein-series. RJW §8 calls it `𝐄`.
- **Sources agree on the standard form:** **yes** on the *mathematics* — constant term =
  (a twist/normalisation of) the p-adic zeta, non-constant coefficients = prime-to-`p` divisor
  sums, with the interpolation `∫ x^{k−1}·𝐄 = E_k^{(p)}`. The search returned a **near-verbatim**
  match to `stabilisedCoeff`: `E*₂ₖ = (1−p^{2k−1})ζ(1−2k)/2 + Σ σ*₂ₖ₋₁(n)qⁿ`.
- **No agreement on a single name / packaging** for the generating power-series object: it is a
  *bootstrap device* whose presentation (measure-valued coefficients vs. `Λ`-valued; the `½`; the
  x-twist; Hida-ordinary vs. Serre) varies by author. It is **not** crystallised into a canonical
  named object the way "Haar measure" or "Dedekind zeta" are.
- **Most general standard form:** the family over weight space / as a `Λ`-adic (or Hida-ordinary)
  modular form; RJW's `Q(ℤ_p^×)⟦q⟧` presentation is one concrete realisation.
- **Generality dimensions where the literature varies:** (a) coefficient ring — measures /
  Iwasawa algebra `Λ` / its fraction field `Q`; (b) normalisation of the constant term (the `½`,
  the x-twist — RJW's bookkeeping); (c) Serre-style elementary vs. Hida-ordinary / Katz-measure
  framing; (d) `p` odd vs. general.
- **Disagreement with the literature:** none on content. The project's framing (the x-twist, the
  erratum #11 "twisted-pseudo-measure" treatment of `A₀`, the `Q(ℤ_p^×)⟦q⟧` ambient) is RJW's
  specific, internally-consistent presentation — a packaging choice, not a contradiction.

The literature search emphatically did **not** come back empty (so the "literature-absence ⇒
narrow/project-specific" branch does not apply): the *concept* is canonical and central. What it
returned is a *family of varied presentations of a bootstrap tool*, which is exactly the
ingredient that makes the verdict turn on packaging/roadmap judgment (Phase 7).

## Phase 4 — Generality analysis

### Generality status table (Phase 4a)

Literature-standard form (from Phase 3): the p-adic / Λ-adic family of Eisenstein series, constant
term = (normalised twist of) the p-adic zeta, non-constant coefficients = prime-to-`p` divisor
sums, characterised by the moment-interpolation `∫ x^{k−1}·𝐄 = E_k^{(p)}`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|--------------------------------|
| 1 | `hp2 : p ≠ 2` | odd prime | family exists for general `p` (the `½` is a normalisation; the un-normalised family is fine at `p = 2`) | yes (in principle) | The `½` forces oddness *here*. Dropping it means renormalising `A₀` (or carrying the family un-halved) — a presentation change tied to the whole `twistedZetaHalf` design, not a local edit. |
| 2 | coefficient ring `Q(ℤ_p^×) = Frac(Λ(ℤ_p^×))` | total fraction ring of the Iwasawa algebra | `Λ`-valued / measure-valued / Hida-ordinary | "more general" framings exist (Hida ordinary families over weight space) | NOT a cheap weakening — it would mean re-founding on a different (larger) substrate. The fraction-ring framing is itself a legitimate modern realisation. |
| 3 | indexing of `A_n` via `divisorMeasure` / `unitOfNat` junk values | prime-to-`p` divisor Diracs with `unitOfNat` junk = 1 on `p ∣ d` | `Σ_{0<d∣n, p∤d} δ_d` | no | Faithful to the source; the junk-value device is the project's encoding of "view `d` as a `ℤ_p^×` unit". |

### Generality verdict (Phase 4b)

**The current form is: NOT cleanly MAXIMALLY GENERAL — but the gap is NOT a cheap mechanical
weakening.** It is one concrete realisation (over `Q(ℤ_p^×)`, with the `½`/x-twist normalisation,
`p` odd) of a canonical object that the literature presents in several strictly-richer framings
(Hida-ordinary families over weight space; general coefficient `𝒪_L`; un-normalised). 

Number of *cheap* weakening opportunities found: **0** (the `p ≠ 2` and coefficient-ring axes are
not local rewrites — they entangle the entire `twistedZetaHalf`/foundation design).

Proposed restatement: **none that is a mechanical generalise-first.** The "more general" target
the literature points at is *a different, larger development* (build the family abstractly over
weight space / as a Hida family), i.e. **building more foundation**, not weakening this signature.
Per `mathlibable-verdicts.md`, that is an EXPENSIVE, whole-development move which is surfaced as a
BORDERLINE "is the bigger object the right target?" question (Phase 7 Q3), **not** a
`YES-but-generalise-first` with a one-shot new signature.

Cost of any genuine generalisation: **EXPENSIVE** (new development, not a re-proof). (Cost does not
by itself downgrade a verdict — but here the issue is that no *cheap, well-defined* restatement
target exists, which is a BORDERLINE driver, not a cost-downgrade.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The object is already built from bundled types (`PadicMeasure`, `FractionRing`, `≃+*` twist); no informal preamble to typeclass-ify. |
| 2 | sequences/metric → filters/topological? | no | — | No sequential/metric limit here; the moments are an algebraic `LinearMap` evaluation. |
| 3 | explicit construction → universal-property class? | partial (not actionable) | One *could* characterise the family by its interpolation property rather than constructing it. | But mathlib has no p-adic-modular-form / weight-space framework to host such a universal property — no downstream to compose with. Not an actionable modernisation today. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | Not a substructure. |
| 5 | vector-space/field-specific → modules/(semi)ring? | no | — | Already over a `CommRing` fraction field via generic `PowerSeries`/`algebraMap`. |
| 6 | 1-categorical → higher-categorical? | no | — | Not a categorical statement. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | The `q`-power index is `ℕ` by definition of a power series; the `ℤ_p^×` parameter is intrinsic. |

**Modern-idiom verdict (Phase 4c):** modern idiom available — **no** (no actionable
modernisation with concrete mathlib downstream). The project *already* uses contemporary idioms
well (bundled `PadicMeasure` linear-functional type, `FractionRing` for `Q`, the twist as a
bundled `RingEquiv`, generic `PowerSeries.mk`). The only "more modern" framing (a universal-
property / weight-space characterisation) has no mathlib substrate to plug into, so it cannot be
claimed as a Bourbaki-2.0 improvement with downstream consequences — it would be abstraction
without a consumer. This is **not** a Phase-4c flip to `YES-but-generalise-first`.

## Phase 4.5 — Diamond / defeq risk assessment (`def`)

### Risk table (Phase 4.5a)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | `eisensteinFamily` is plain *data* (a `PowerSeries` term), not an `instance` and not a type/structure carrying algebraic instances. It introduces no new typeclass-search path; the `PowerSeries (QuotientField p)` ring/algebra instances are mathlib's existing ones on `PowerSeries`/`FractionRing`. |
| 2 | Reducibility leak | **none** | Sealed `noncomputable def` (no `@[reducible]`). The body uses `PowerSeries.mk` + `if`; nothing forces defeq exposure. `constantCoeff`/`coeff` rewrites in the consumer go through `PowerSeries.coeff_mk` and an explicit `from rfl`, i.e. controlled unfolding, not ambient defeq. |
| 3 | Non-canonical unfolding | **low** | The `n = 0` branch needs `constantCoeff (eisensteinFamily …) = twistedZetaHalf …` which the file proves `from rfl` (`:393`), and `coeff_mk`/`if_neg` for `n ≠ 0` (`:398`). This is normal `PowerSeries.mk` behaviour; no surprising `simp` unfolding. If upstreamed, one would add `@[simp]` `constantCoeff_eisensteinFamily` / `coeff_eisensteinFamily` lemmas — standard. |
| 4 | Instance priority collision | **n/a** | Not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | All types are concrete (`ℕ`-indexed `PowerSeries` over the fixed `Q(ℤ_p^×)`); no universe variables, no forced annotations. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort` introduced. The `algebraMap _ _ (divisorMeasure p n)` is an explicit ring map `Λ → Q`, not a coercion competing with mathlib's. |

### Risk verdict (Phase 4.5)

**Overall risk: NONE.** Top risks: none. (`eisensteinFamily` is well-behaved *as a definition* —
the obstacles to mathlib inclusion are entirely about the *substrate/roadmap*, Phases 3–7, not
about defeq/diamond infrastructure hazards. So Phase 4.5 imposes no extra constraint on the
Phase-7 gate.)

## Phase 5 — Mathlib five-method search

Searched for both the user's form (`eisensteinFamily` / Λ-adic Eisenstein family power series over
`Q(ℤ_p^×)`) and the literature-standard form (p-adic Eisenstein family / Eisenstein measure /
Hida family of Eisenstein series / Kubota–Leopoldt / p-adic L-function) and the underlying
primitives.

| Method | Tool | Query | Result |
|--------|------|-------|--------|
| A | Lean-Finder | — | **n/a**: no Lean MCP / Lean-Finder available this session (consistent with all sibling reports in this batch). Concept-level AI search covered by Phase 3 web channels. |
| B | Loogle (`lean_loogle`) | — | **n/a**: no Lean MCP this session. |
| C | LeanSearch (`lean_leansearch`) | — | **n/a**: no Lean MCP this session. |
| D | grep mathlib src | `eisenstein` (case-insensitive), `padic.*eisenstein`, `eisenstein.*family`, `eisensteinFamily`, `adicEisenstein` | Only **classical complex** Eisenstein series: `Mathlib/NumberTheory/ModularForms/EisensteinSeries/*` (`Basic`, `Defs`, `QExpansion`, `E2/*`, `Summable`, `UniformConvergence`, …), `TsumDivisorsAntidiagonal`, `Analysis/SpecialFunctions/…/Cotangent`. **0 hits** for any p-adic / family / measure-valued Eisenstein object. |
| D | grep mathlib src | `kubota`, `leopoldt`, `padicZeta`, `padicLFunction`, `p-adic L-function`, `p-adic zeta` | **0 hits.** Mathlib has no Kubota–Leopoldt / p-adic zeta / p-adic L-function. |
| D | grep mathlib src | `hida`, `overconvergent`, `padicModular`, `p-adic modular`, `Lambda-adic`, `LambdaAdic`, `weightSpace`, `Amice`, `measure.*PowerSeries`, `Iwasawa.*PowerSeries` | **0 relevant hits.** (The `genWeightSpace`/`weightSpace` hits are Lie-theory `RootSystem`, unrelated.) No Hida theory, no overconvergent / p-adic modular forms, no Λ-adic forms, no Eisenstein/Iwasawa measure-generating series. |
| E | name-pattern grep | `PadicMeasure`, `QuotientField`, `Λ(ℤ_p^×)`, pseudo-measure, `PowerSeries.mk` over `FractionRing`-of-measures | `PowerSeries.mk` exists as *generic* infra (`RingTheory/PowerSeries/Basic.lean:109`); `FractionRing`/`IsLocalization`/`PowerSeries`/`algebraMap` exist generically. **None instantiated for `PadicMeasure`/`Λ(ℤ_p^×)`**; the `C(X,ℤ_[p]) →ₗ ℤ_[p]` "p-adic measure" is not a mathlib concept (mathlib's `MeasureTheory.Measure` is the σ-additive notion). |

### Mathlib search-status (Phase 5)

**Concluded: "not in mathlib (all available methods exhausted, plus the literature-standard
form)".** Mathlib has neither `eisensteinFamily` nor any p-adic / Λ-adic Eisenstein family,
Eisenstein measure, Hida family, p-adic zeta, p-adic L-function, Iwasawa algebra, or p-adic
measure type. Only the generic power-series / localisation / `algebraMap` plumbing and the
*classical complex* Eisenstein series exist. → **not `NO-mathlib-has-it`.**

## Phase 6 — Composition check + call-sites

### Call sites — `eisensteinFamily` (Phase 6.0)

```
Internal use count (within PadicLFunctions, excluding the declaring file):  K = 0
External-to-file callers:                                                    0 distinct files
Repo-wide (all projects, excluding the declaring file):                      0
```

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `EisensteinFamily.lean:382` | `… * PowerSeries.constantCoeff (eisensteinFamily p hp2)` (in `eisensteinFamily_interpolation`, same file) |
| `EisensteinFamily.lean:387` | `PowerSeries.coeff n (eisensteinFamily p hp2)` (same file) |
| `EisensteinFamily.lean:393` | `… constantCoeff (eisensteinFamily p hp2) = twistedZetaHalf p hp2 from rfl` (same file) |
| `EisensteinFamily.lean:398` | `rw [eisensteinFamily, PowerSeries.coeff_mk, if_neg hn]` (same file) |

Inline-derivation grep (was the family re-built inline elsewhere without `eisensteinFamily`?):
**(none)** — the object appears nowhere outside its own file.

**What the call-sites pattern tells you.** `eisensteinFamily` is used **only** by its own
interpolation theorem `eisensteinFamily_interpolation` (the named RJW §8 result), within the same
file. `K = 0` external consumers. This is *not* a "dead wrapper consumers bypass" — it is the
**headline object** of the file, and the interpolation theorem is precisely the statement that
gives it meaning. But the `K = 0`-outside-its-own-file pattern means it is currently a *terminal*
object: nothing downstream depends on it yet (Part I closer). Combined with Phase 2's BIG/main-
result status, this is a YES-leaning *content* signal undercut by a "no consumers / sits atop an
unupstreamed tower" *roadmap* signal — exactly the tension that lands the verdict in BORDERLINE.

### Composition check (Phase 6a)

Can `eisensteinFamily` be derived from mathlib in ≤3 chained calls?

- **Attempt 1:** `PowerSeries.mk (fun n => if n = 0 then <A₀> else algebraMap _ _ (<A_n>))`.
  - Mathlib decls used: `PowerSeries.mk` (generic), `algebraMap` (generic).
  - Result: **fails as a mathlib composition** — the *coefficients* `<A₀> = twistedZetaHalf` and
    `<A_n> = divisorMeasure` are project-local objects built on `PadicMeasure`, `Λ(ℤ_p^×)`,
    `Q(ℤ_p^×)`, `padicZeta`, the x-twist — **none of which exist in mathlib**. `PowerSeries.mk`
    is just the container; it does not "give us" the family, because the substance is the absent
    coefficients.
  - Notes: the only mathlib content is the trivial `mk`-of-a-piecewise-function packaging; the
    mathematics is entirely in the (absent) coefficient construction.

**Conclusion: NOT-COMPOSABLE from mathlib.** The building blocks (`twistedZetaHalf`,
`divisorMeasure`, `QuotientField`, `padicZeta`, `quotientTwist`) are themselves absent from
mathlib. → **not `NO-composable-from-mathlib`.**

## Phase 7 — Verdict

## Verdict: `PadicLFunctions.eisensteinFamily`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the Λ-adic / Serre–Wiles–Katz Eisenstein family is **canonical
  and central** (near-verbatim match to `stabilisedCoeff`; "the p-adic zeta is the constant term
  of a p-adic Eisenstein family"), but presented across the literature in *varied framings* as a
  *bootstrap tool*, with **no single universal named generating-series object**.
- Generality analysis (Phase 4): NOT cleanly MAXIMALLY GENERAL, but **no cheap mechanical
  weakening** exists — the "more general" target is a *larger development* (Hida/weight-space
  family), which is EXPENSIVE foundation-building, not a generalise-first restatement. Phase 4c:
  no actionable modernisation (already idiomatic; no mathlib substrate for a universal-property
  framing).
- Diamond/defeq risk (Phase 4.5): **NONE** (well-behaved data `def`; no infra hazard).
- Mathlib search (Phase 5): **not in mathlib** — no p-adic/Λ-adic Eisenstein family, Eisenstein
  measure, Hida family, p-adic zeta, Iwasawa algebra, or p-adic measure type; only generic
  `PowerSeries`/`algebraMap` plumbing and the classical complex Eisenstein series.
- Composition check (Phase 6): **NOT-COMPOSABLE** (the coefficient building blocks are themselves
  absent from mathlib); call-sites **K = 0** outside the declaring file (terminal headline object,
  used only by its own interpolation theorem).

**Rationale.** Three of the five buckets are decisively excluded by the evidence.
`NO-mathlib-has-it` is out: Phase 5 found mathlib has none of this (no p-adic L / Kubota–Leopoldt,
no Iwasawa algebra, no p-adic measures, no p-adic Eisenstein family). `NO-composable-from-mathlib`
is out: Phase 6 is NOT-COMPOSABLE because the coefficient objects (`twistedZetaHalf`,
`divisorMeasure`, `padicZeta`, `quotientTwist`) do not exist in mathlib — `PowerSeries.mk` is an
empty container without them. `YES-add-as-is` is out: this terminal `def` sits atop an **entire
project-local prerequisite tower** (`PadicMeasure` on `ℤ_p^×`, the Iwasawa algebra `Λ(ℤ_p^×)`, its
total fraction ring `Q(ℤ_p^×)`, the pseudo-measure formalism, `padicZeta`, the x-twist) — *none*
of which is in mathlib, and several of whose pieces were themselves assessed BORDERLINE
(`twistedZetaHalf`, `divisorMeasure`, `unitsTwist`, `sigmaP`). A keystone object cannot be "added
as-is" ahead of its whole foundation. `YES-but-generalise-first` is out as the headline verdict
too: Phase 3 does **not** hand us a strictly-more-general *named form of this very object* to
restate into via `/generalise`; the literature's "more general" thing is a *different, larger
development* (the Hida-ordinary / weight-space family), i.e. building more foundation — an
EXPENSIVE whole-development move that `mathlibable-verdicts.md` explicitly says to surface as a
BORDERLINE "is the bigger object the right target?" question, not a mechanical generalise-first.

What remains is genuine human judgment, exactly what `BORDERLINE-needs-human` is for: (a) which
object is the real mathlib target — the *family* `eisensteinFamily`, its *interpolation theorem*
`eisensteinFamily_interpolation`, or `padicZeta` itself (the family has `K = 0` consumers and is
the Part-I closer); (b) whether upstreaming the whole p-adic-measure / Iwasawa-algebra / p-adic-
zeta foundation to mathlib is a goal at all (a project/community-policy call — every coefficient
and twist piece carries the same gate); and (c) the normalisation/encoding choices (the `½`, the
x-twist, `p ≠ 2`, the `Q(ℤ_p^×)⟦q⟧` ambient) that determine what the *natural mathlib form* of the
family would even be. This verdict is also fully consistent with the already-recorded verdicts of
its two coefficient sources (`twistedZetaHalf` → BORDERLINE, `divisorMeasure` → BORDERLINE) and is
the precise object that `twistedZetaHalf`'s Q3 asks about ("is the headline the *family*?").

**Refactor-actionable bar — numbered questions (≤5):**

1. **Which object is the mathlib target?** The mathlib-worthy headline is plausibly the *family*
   `eisensteinFamily` **together with** its interpolation theorem `eisensteinFamily_interpolation`
   (with `A₀`, `A_n` as internal coefficients), or alternatively `padicZeta` itself. Do you want
   `eisensteinFamily` as a standalone public `def`, or should the family + interpolation be a
   single packaged contribution (and is `padicZeta` the more fundamental target)?
2. **Foundation-first (policy).** `eisensteinFamily` cannot reach mathlib before its whole tower
   (`PadicMeasure` on `ℤ_p^×`, `Λ(ℤ_p^×)`, `Q(ℤ_p^×)`, the pseudo-measure formalism, `padicZeta`,
   the x-twist `quotientTwist`/`unitsTwist`). Is upstreaming that **foundation** a goal? If no, this
   stays project-local and the question is moot; if yes, this `def` is the keystone leaf of that
   effort, shipped only as part of it.
3. **`½` / x-twist / `p ≠ 2` encoding.** The constant coefficient is `twistedZetaHalf` (x-twist of
   `padicZeta`, halved, hence `p ≠ 2`), and per erratum #11 it is a *twisted-pseudo-measure*, not a
   pseudo-measure. Is this RJW-specific normalisation the form mathlib should carry, or would
   mathlib prefer the un-twisted `x·ζ_p` / `ζ_p` with the half/twist applied at family-assembly
   time? (This determines the natural mathlib signature of the whole family.)
4. **Coefficient-ring framing.** Should the family live over `Q(ℤ_p^×) = Frac(Λ(ℤ_p^×))` (as now),
   or would mathlib prefer the more general Hida-ordinary / weight-space framing the literature
   uses (a larger development)? This is the "is the bigger object the right target?" generality
   call from Phase 4.
5. **Naming.** If kept as a `def`, is `eisensteinFamily` the right mathlib name (vs.
   `padicEisensteinFamily`, `lambdaAdicEisensteinFamily`, `eisensteinMeasure`), given the
   literature uses several names for this object?

**Next action:** user answers the questions; re-run `/mathlibable PadicLFunctions.eisensteinFamily`
to resolve the verdict. Likely resolutions:
- Q2-no, or Q1→`padicZeta`/the-interpolation-theorem ⇒ drop `eisensteinFamily` from independent
  mathlib consideration (it ships, if at all, only as an internal object of a much larger
  upstreaming; rename/keep project-local).
- Q2-yes + Q1→keep-named-family ⇒ still BORDERLINE on Q3–Q5 (the `½`/twist/coefficient-ring/name
  encoding), to be settled via `/generalise` before any PR — and **only after the foundation
  lands**.

## Phase 8 — Report (this document)

Written to
`projects/PadicLFunctions/.mathlib-quality/overview/mathlibable/PadicLFunctions.eisensteinFamily.md`.

**Final verdict: `BORDERLINE-needs-human`.**

---

### Sources (Phase 3)
- https://arxiv.org/pdf/2309.15692 — Rodrigues Jacinto–Williams, *An introduction to p-adic
  L-functions* (the project's source; §8 = TeX 2361–2446)
- https://people.math.harvard.edu/~smarks/notes/p-adic-mfs.pdf — Marks, *p-adic Modular Forms à la
  Serre* (Serre bootstrap; `E*₂ₖ = (1−p^{2k−1})ζ(1−2k)/2 + Σ σ*₂ₖ₋₁(n)qⁿ`)
- https://maths-people.anu.edu.au/banerjeed/lectures.pdf — *Λ-adic forms and the Iwasawa Main
  Conjecture* (Λ-adic Eisenstein family; Wiles's "standard example")
- https://arxiv.org/pdf/1204.3878 — *Analytic constructions of p-adic L-functions and Eisenstein
  series*
- https://arxiv.org/pdf/2101.01879 — Eischen, *An introduction to Eisenstein measures*
- https://www.ams.org/journals/bull/1997-34-01/S0273-0979-97-00696-4/S0273-0979-97-00696-4.pdf —
  Hida, *Elementary theory of L-functions and Eisenstein series* (Wiles realises Deligne–Ribet
  p-adic L as constant terms of a Hida family of Eisenstein series)
- https://sites.math.duke.edu/~dasgupta/papers/EvilEisenstein.pdf — Bellaïche–Dasgupta,
  *The p-adic L-functions of evil Eisenstein series*
- https://ncatlab.org/nlab/show/Eisenstein+series — nLab (classical complex only; **no** p-adic /
  Λ-adic family)
