# `/mathlibable` report — `PadicLFunctions.MeasureR.extLog_eq_padicLog_of_norm_lt_one`

**Final verdict: `BORDERLINE-needs-human`** (the lemma is the internal compatibility
glue between two *project-specific* p-adic-logarithm definitions, `extLog` and
`padicLog`; its mathlib-worthiness is inherited from un-made decisions about those
parent definitions and about whether mathlib wants one p-adic log or two).

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — the
  AINTLIB build is stale/slow; declaration + dependencies read directly from source).
- decl `PadicLFunctions.MeasureR.extLog_eq_padicLog_of_norm_lt_one`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:590`
- kind:                      theorem
- has sorry:                 no (proof body is a complete ~10-line `obtain`/`rw` argument)
- module docstring summary:  "The p-adic value L_p(θ,1) (RJW §6.2, Thm 6.1(ii), decomposition P6)" —
  the file develops the explicit antiderivative / Mahler-transform route to Leopoldt's
  formula for `L_p(θ,1)`; `extLog` constants appear in the antiderivative power series.

---

### Statement (Phase 1)

`extLog_eq_padicLog_of_norm_lt_one` is a **theorem** stating the following:

> Let `K` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra (the
> intended models are `ℚ_p`, `ℂ_p`, and finite/complete extensions of `ℚ_p`). The
> **extended (Iwasawa-branch) p-adic logarithm** `extLog p` and the **power-series
> p-adic logarithm** `padicLog p` coincide on the whole open unit ball
> `{x : ‖x − 1‖ < 1}`. In symbols, `extLog p x = padicLog p x` whenever `‖x − 1‖ < 1`.

Mathematical background (the two objects):
- `padicLog p x = ∑' n, (−1)ⁿ (n+1)⁻¹ • (x−1)^(n+1)` (`PadicExp.lean:384`) — the naive
  Mahler/Taylor series `log(1+t) = ∑ (−1)ⁿ⁺¹ tⁿ/n`, junk-total, genuinely convergent &
  meaningful for `‖x−1‖ < 1`.
- `extLog p x` (`ExtLog.lean:286`) — Iwasawa's *extension* normalized by `log_p p = 0`:
  defined on `ExtLogDomain` (rational-valuation elements `x^m = p^k·y` with `y−1` in the
  exponential ball) by `extLog x = (m : ℚ_p)⁻¹ • padicLog y`, and `0` off the domain.
  The file's docstrings cross-reference **Washington, *Introduction to Cyclotomic Fields*,
  §5.1** and "Iwasawa's branch `log_p(p) = 0`".

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]` — a complete ultrametric normed `ℚ_p`-algebra (the natural home of
  the p-adic log; covers `ℂ_p`). `[CharZero K]` is present on the file's `variable` line
  but **`omit`-ted** for this theorem (unused).

Hypotheses (Lean side):
- `(hx : ‖x − 1‖ < 1)` — `x` lies in the open unit ball, i.e. `x` is a principal unit
  (`x ≡ 1`), the region where the defining power series converges.

Conclusion (math): the Iwasawa-extended log restricts to the convergent power-series log
on the principal-unit ball.

Conclusion (Lean): `extLog p x = padicLog p x`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper/bridging lemma — neither a `def`/`class`/`structure` introducing a new
structure, nor a named main result. It is an *agreement* lemma between two already-defined
objects. (It is, however, the compatibility identity tying the extended-log definition to
its convergent series — a small lemma about big objects.)

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is narrative only.)

### One-line check (Phase 2b)

Body line count: ~10 substantive lines (multi-line proof)
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Iwasawa p-adic logarithm agrees with power series log on unit ball ‖x−1‖<1"                            | yes  | extension *defined* to agree with the series on `\|z−1\|<1`; base case of Iwasawa's construction | Warwick & LTCC lecture notes; MIT 18.785 PS10; pari-users thread all give the construction "raise to a power until ≡1, plug into the series" |
|  2 | WebSearch (general form / def)   | "p-adic logarithm definition power series convergence Iwasawa branch log_p(p)=0 extension to Cp*"       | yes  | `log_p(z) = −∑ (1−z)ⁿ/n` for `\|z−1\|<1`, extended to `ℂ_p^×` by `log_p p = 0`, `log_p w = 0` (w root of unity), multiplicatively | Montreal Appendix 16.6; Wikipedia "p-adic exponential function"; converges since `\|xⁿ/n\| ≤ λⁿ p^{v_p(n)} → 0` |
|  3 | WebSearch (named-after / source) | "Washington Introduction Cyclotomic Fields p-adic logarithm section 5.1 extended log_p definition"      | yes  | `α = p^r w x`, `x∈U₁`; set `log_p p = log_p w = 0`; **`log_p` on `\|x\|<1` uniquely extended to all of `ℂ_p^×`** with `log xy = log x + log y`, `log p = 0` | This *is* the source the project docstrings cite (Washington §5.1). The extension restricting to the series on `U₁` is exactly the present lemma. |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution)                                          | n/a  | —                                | **n/a — ChatGPT MCP not configured in this environment** (no ChatGPT tool surfaced; only Asana/Atlassian/Box auth proxies). The "standard form + generality" question this channel would answer is fully covered by rows 1–3, which agree. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/`                               | n/a  | (no references dir)                | `.mathlib-quality/references/` and `refs/` both absent — recorded n/a. (Project docstrings already pin Washington §5.1 as the source.) |
|  6 | nLab                             | "nLab p-adic logarithm Iwasawa logarithm definition"                                                   | partial | confirms series def + `log_p p = 0` Iwasawa normalization; image-on-principal-units context | no dedicated nLab page surfaced; results re-confirm the standard construction |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | n/a — not a categorical concept; the p-adic log is a concrete analytic function, no universal-property framing in the literature |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | n/a — not an algebraic-geometry concept; this is p-adic analysis, outside Stacks' scope |
|  9 | MathOverflow / Math.StackExchange| "p-adic logarithm extended coincides power series principal units restriction"                         | yes  | `log_p(1+x) = x − x²/2 + …` converges on `m_K`; `log_p : 1+m_K^r → m_K^r` iso for `r > e/(p−1)`; extension to `ℂ_p^×` via `log_p p = log_p w = 0` | arXiv 1904.09850 / 1907.06437 ("image of p-adic log on principal units") give the precise restriction/extension picture |
| 10 | recent arXiv (last 5 years)      | (covered by rows 1,2,9 — arXiv 1907.06437 2023, 1904.09850, 2410.20934, 2304.02789)                    | yes  | same construction; actively used in Ankeny–Artin–Chowla / Iwasawa-theory papers | the series-vs-extension agreement is treated as standard background, never as a theorem worth a label |

Protocol pass check:
- WebSearch ran **3 distinct queries at different generality levels** (rows 1–3): specific
  agreement form, general definition+extension, named source. ✓
- ChatGPT MCP: **n/a — not configured in this environment** (one-line reason given; its
  question is subsumed by rows 1–3, which are mutually consistent). ✓ (environment n/a)
- Local references: checked, **n/a — directory absent**. ✓
- nLab: **checked** (row 6). ✓
- Stacks / nCatLab / MathOverflow / arXiv: each checked or n/a-with-reason (rows 7–10). ✓

### Literature summary (Phase 3)

Concept identified as: **the (Iwasawa) p-adic logarithm** `log_p`, in two guises — the
*convergent power series* `log(1+t) = ∑ (−1)ⁿ⁺¹ tⁿ/n` on the principal-unit ball, and its
*Iwasawa extension* (`log_p p = 0`, `log_p w = 0`) to `ℂ_p^×`. The present lemma is the
**restriction identity**: the extension agrees with the series on `‖x−1‖<1`.

Sources agree on the standard form: **yes** — every source (Washington §5.1, Iwasawa,
Koblitz, the lecture notes, arXiv NT papers) defines `log_p` by the series on `‖x−1‖<1`
*first*, then extends. The agreement on the ball is therefore **the construction's base
case / defining compatibility**, treated everywhere as immediate background, not as a
named theorem.

Most general standard form: `log_p` on a complete (ultrametric) extension field of `ℚ_p`
— canonically `ℂ_p`; the series-vs-extension agreement holds on the principal-unit ball
`‖x−1‖<1` of any such field.

Generality dimensions where the literature varies:
  - Coefficient field: from `ℚ_p` / `ℤ_p` up to `ℂ_p` (and any complete subfield). The
    most general is "any complete ultrametric extension of `ℚ_p`". The Lean form's
    `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`
    **matches this maximally-general home exactly**.
  - Domain of the extended log: literature extends to all `ℂ_p^×`; the project's `extLog`
    extends to `ExtLogDomain` (rational-valuation elements). On the *ball* (this lemma's
    hypothesis) the two pictures coincide, so this dimension does not affect the lemma.

Disagreement with the literature: **none** — the Lean statement is exactly the standard
restriction identity, at the standard (maximal) generality.

---

### Generality analysis — `extLog_eq_padicLog_of_norm_lt_one`

Literature-standard form (from Phase 3): the Iwasawa-extended `log_p` on a complete
ultrametric extension of `ℚ_p` restricts to the convergent power series on the
principal-unit ball `‖x−1‖<1`.

| # | Parameter / hypothesis                  | Current Lean form                       | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------|------------------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | `[NormedField K]`                       | normed field                             | complete ultrametric ext. of `ℚ_p` | NO                  | the field structure is needed (`extLog`/`padicLog` are field-valued; division by `(p^j)` scalar) |
| 2 | `[NormedAlgebra ℚ_[p] K]`               | normed `ℚ_p`-algebra                     | `K ⊇ ℚ_p` complete                  | NO                  | the `(m:ℚ_p)⁻¹` scalar in `extLog` lives in `ℚ_p`; the algebra structure is what makes the scaling meaningful |
| 3 | `[IsUltrametricDist K]`                 | ultrametric                              | non-arch. (ultrametric)             | NO                  | convergence of `padicLog` and the exp-ball machinery use the ultrametric inequality essentially |
| 4 | `[CompleteSpace K]`                     | complete                                 | complete (`ℂ_p` is)                 | NO                  | `padicLog` is a `tsum`; needs completeness to converge to a value |
| 5 | `(hx : ‖x − 1‖ < 1)`                    | principal unit                           | `\|x−1\|<1` (radius-1 ball)          | NO                  | this is exactly the convergence radius of the series; cannot be weakened (series diverges outside) |
| 6 | `[CharZero K]` (file var)               | **omit-ted** (unused)                    | char 0 (automatic from `ℚ_p`-alg)   | already dropped     | the theorem already `omit [CharZero K]` — char-zero is not assumed |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**
Number of weakening opportunities found: **0** (the one redundant hypothesis, `CharZero K`,
is already `omit`-ted).
Proposed restatement: none — the typeclass cluster is precisely the literature's
maximal home (`ℂ_p`-type fields), and the ball hypothesis is the exact convergence radius.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "Let K be a foo" preambles → typeclasses?                                                                   | no       | already fully typeclass-based (`NormedAlgebra ℚ_[p] K`, etc.) | — |
|  2 | sequences/metric → filters/topological?                                                                     | no       | the statement is a pointwise equality at a single `x`; no limit to filter-ise | — |
|  3 | construct an object where a universal property would characterise it?                                       | **see note** | not for *this lemma*, but the *parent defs* `extLog`/`padicLog` are the relevant question | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                          | no       | no substructure here | — |
|  5 | vector-space/field-specific → weaken to module/(semi)ring?                                                  | no       | a p-adic log is intrinsically field-valued; no further algebraic weakening | — |
|  6 | 1-categorical → higher-categorical?                                                                         | no       | concrete analytic function | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid?                                                            | no       | the only index is the prime `p`, fixed | — |

**Note on the real modern-idiom question.** The genuine Bourbaki-2.0 question here is *not*
about this lemma's signature — it is about its **two parent definitions**. Mathlib has **no
p-adic logarithm at all** (Phase 5). When mathlib eventually adds one, the idiomatic design
would plausibly be a **single** p-adic/ultrametric logarithm (the Iwasawa-branch extension),
with the convergent-series formula proved as one of its *characterizing lemmas* — rather
than two co-existing definitions (`padicLog` the series + `extLog` the extension) plus a
bridge between them. Under that design, the present theorem `extLog = padicLog on the ball`
would **not exist as a standalone result**: it would be the definitional content of, or an
immediate corollary of, the single log's defining property. This is a real organisational
question, but it is a question about the *definitions*, which this skill cannot resolve for
a dependent lemma in isolation (see Phase 7).

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but at the level of the parent definitions, not this lemma.**
- The lemma's own signature is already maximally idiomatic and general.
- The modern-idiom improvement ("one p-adic log, not two + a bridge") is a decision about
  `extLog`/`padicLog`. If taken, this bridging lemma is absorbed and disappears.
- One-line reason this is not a *lemma-level* modernisation move: there is nothing to
  re-state about `extLog p x = padicLog p x` itself; the modernisation acts on the objects
  being equated, not on the equation.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or
typeclass-search paths). Skipped.

---

### Mathlib search-status: `extLog_eq_padicLog_of_norm_lt_one`

(Searched against pinned mathlib `d90090f647ca`, Lean `v4.31.0-rc2`, at
`.lake/packages/mathlib/Mathlib/`.)

[A] Lean-Finder       — n/a (tool not available in this environment; substituted by [C]/[D]/[E] + WebSearch of mathlib4 docs)
[B] Loogle            — n/a (tool not available; the type `extLog p x = padicLog p x` references project-only constants `extLog`/`padicLog`, so a Loogle type-pattern query is vacuous — neither constant exists in mathlib to pattern against)
[C] LeanSearch / docs — WebSearch "mathlib lean4 p-adic logarithm padicLog Padic.log exists": **no hit** — mathlib4 docs for `NumberTheory/Padics/` define `ℚ_[p]`, `ℤ_[p]` as normed field/ring but document **no p-adic logarithm / exponential**
[D] Grep mathlib src  — `grep -rin "extlog|padiclog|p-adic log|padic_log|iwasawa log"` over all of `Mathlib/`: **no hits**. `NumberTheory/Padics/` has no Exp/Log file. The only `*Log*` in `NumberTheory/Padics/` is `Nat.log p n` inside `padicValNat_factorial` — the integer logarithm in valuation bounds, **unrelated**.
[E] Name pattern      — `def/theorem *Log*` in `NumberTheory/Padics/`: only `padicValNat_*` (integer `Nat.log`). General `Analysis/SpecialFunctions/Log/` has `Real.log`, `Complex.log`, `ENNReal` logs — **none p-adic, none ultrametric**. Mathlib has `NormedSpace.exp` (general exponential) but **no general analytic `log` inverse to it**, and certainly none over `ℚ_p`.

Searched for both:
  - the user's current form (`extLog = padicLog` on the ball) — **not in mathlib**;
  - the literature-standard form (Iwasawa `log_p` restricts to its defining series on
    `‖x−1‖<1`) — **not in mathlib**, because mathlib has no p-adic `log_p` to state it about.

Concluded: **not in mathlib** (all available methods exhausted, both forms). More strongly:
**neither object in the statement (`extLog`, `padicLog`) exists in mathlib** — the entire
p-adic logarithm theory is project-local. Mathlib offers no building blocks specific to this
identity.

---

### Call sites — `extLog_eq_padicLog_of_norm_lt_one`

Internal use count: **2** (within `projects/PadicLFunctions/`, NOT counting the declaring
theorem's own body). Plus 1 docstring mention.
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`); the second use is in a
*different* theorem within the same `ValuesAtOne.lean`.

| Caller file:line              | Usage pattern (one-line excerpt)                                                       |
|-------------------------------|-----------------------------------------------------------------------------------------|
| ResidueZeta.lean:1377         | `rw [← MeasureR.extLog_eq_padicLog_of_norm_lt_one (p := p) (…) , extLog_eq_zero_of_pow_eq_one …]` — converts a `padicLog(ξ^i)=0` goal (root of unity) into an `extLog` fact |
| ValuesAtOne.lean:1083         | `… extLog_mul p (…) (…), extLog_eq_padicLog_of_norm_lt_one (p := p) hwsub]` — in a `seriesEval_logSeriesAt` computation, swaps `extLog` for `padicLog` on the ball factor |
| ValuesAtOne.lean:1345 (doc)   | docstring: "layer (`extLog_eq_padicLog_of_norm_lt_one` / `padicLog_pow_p_of_norm_lt_one`, …)" |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none found) — the only sibling, `extLog_eq_padicLog` (`ExtLog.lean:351`), is the
    *narrower* exp-ball version; this `_of_norm_lt_one` version is the unique unit-ball one
    and is reused, not re-derived.

Composability signal: **K = 2 internal uses, no inline re-derivation** → a real internal
API tie used in two genuine computations. Within the project this is load-bearing glue.
(But "load-bearing inside this project" is a different question from "belongs in mathlib";
see Phase 7.)

### Composition check (Phase 6)

Can `extLog_eq_padicLog_of_norm_lt_one` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: any mathlib composition.
  - Mathlib decls used: **none available** — `extLog`, `padicLog`, `ExtLogDomain`,
    `InExpBall`, `exists_pPow_pow_inExpBall`, `extLog_eq_of_witness`,
    `padicLog_pow_pPow_of_norm_lt_one` are **all project-local** (each defined in exactly
    one project file; none in mathlib).
  - Result: **fails** — mathlib cannot even express the statement.

Attempt 2 (from project primitives, for completeness — NOT a mathlib composition): the
actual proof picks a witness `j` via `exists_pPow_pow_inExpBall`, applies
`extLog_eq_of_witness` with `(m,k,y) = (p^j, 0, x^{p^j})`, rewrites with
`padicLog_pow_pPow_of_norm_lt_one`, then cancels the `(p^j)⁻¹` vs `(p:K)^j` scalars (a
cast + `smul_smul` + `inv_mul_cancel₀`). That is **~10 lines of genuine reasoning across 3
project lemmas + a scalar-cast argument** — not a 1–3 call composition, and entirely
project-internal regardless.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The statement is not even expressible in
mathlib terms, let alone composable in ≤3 calls.

---

## Verdict: `extLog_eq_padicLog_of_norm_lt_one`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the Iwasawa p-adic log is *defined by* the convergent series
  on `‖x−1‖<1` and *then extended* (Washington §5.1, Iwasawa, Koblitz, lecture notes,
  arXiv NT). The series-vs-extension agreement on the ball is the **construction's base
  case** — universally treated as immediate background, never as a labelled theorem.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — the typeclass cluster is the
  literature's maximal home (`ℂ_p`-type complete ultrametric `ℚ_p`-algebras); the ball
  hypothesis is the exact convergence radius; the one redundant hypothesis (`CharZero`) is
  already `omit`-ted. Modern-idiom (4c): the only real improvement is at the **parent-def**
  level ("one p-adic log, not two + a bridge"), not at this lemma's signature.
- Mathlib search (Phase 5): **not in mathlib**, and neither `extLog` nor `padicLog` exists
  in mathlib — the entire p-adic logarithm theory is absent from mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (statement not even
  expressible there); 2 genuine internal call sites, no inline re-derivation.

**Rationale (why BORDERLINE rather than a YES or a NO):**

Mechanically the lemma looks like a YES: mathlib has no p-adic logarithm at all, the fact is
standard and at maximal generality, it is not composable from mathlib, it is sorry-free, and
it has two real internal consumers. Were this an independent result, that profile points to
`YES-add-as-is`.

But this theorem is **not an independent result** — it is the *internal compatibility glue
between two co-defined project objects*, `extLog` (Iwasawa extension) and `padicLog`
(convergent series). The skill's own def-first principle is decisive: **a lemma's
mathlib-verdict is inherited from its parent definitions' verdicts**, and those parents have
**not been assessed** (only sibling lemmas like `padicLog_pow_p_of_norm_lt_one` have
`mathlibable` files; `extLog`/`padicLog` themselves do not). Two judgment calls — neither
groundable from the lemma in isolation — sit upstream of this verdict:

1. **Does mathlib want *these* two definitions, in *this* form?** `padicLog` is junk-total
   via a bare `tsum`; `extLog` is junk-total via a `Classical.choice` over `ExtLogDomain`
   with the bespoke witness construction `m⁻¹ • padicLog y`. Whether mathlib should adopt
   these specific designs (vs. e.g. a single bundled log, or a `PartialHom`/`Set`-domain
   formulation) is a definitional-taste decision for a mathlib maintainer.

2. **One p-adic log or two?** Phase 4c surfaced the genuine Bourbaki-2.0 move: the
   idiomatic mathlib design is plausibly a *single* Iwasawa-branch p-adic log, with the
   power-series formula as one of its *characterizing lemmas*. Under that design **this
   theorem is absorbed and ceases to exist as a standalone result** — it becomes the
   defining property (or a one-line corollary) of the single log. So the lemma's very
   existence as a separate declaration is contingent on a design choice not yet made.

Because the verdict flips entirely on these upstream decisions (YES-add-as-is if mathlib
adopts the two-definition design as-is; absorbed/NO-it-disappears if mathlib takes the
one-log modern idiom), and because the parent defs have not themselves been run through
`/mathlibable`, the honest verdict is **BORDERLINE-needs-human** — exactly the
"verdict depends on a judgment call (definitional taste + API design) the skill can't make
alone" situation, and the closest analog to Case 5 in the verdict reference (a
project-specific analytic-NT object whose mathlib form depends on un-made API decisions).

**Numbered questions for the user (≤5):**

1. **Assess the parents first.** Should `extLog` and `padicLog` be run through
   `/mathlibable` *before* this lemma? This lemma's verdict is downstream of theirs; if both
   parents are `YES`, this becomes `INHERITED-YES` (ships as their compatibility lemma); if
   the parents are reshaped, this lemma may not survive.

2. **One log or two?** For a mathlib p-adic logarithm, do you want a **single** Iwasawa-branch
   `log_p` (extension to rational-valuation / `ℂ_p^×`) with the convergent-series formula as
   a *characterizing lemma* — in which case `extLog = padicLog on the ball` is absorbed into
   that lemma and should **not** be shipped separately? Or two co-existing definitions plus
   this explicit bridge (the current project design)?

3. **Junk-totality conventions.** Are the project's junk-total designs (`padicLog` via bare
   `tsum`; `extLog` via `Classical.choice` over `ExtLogDomain`, `0` off-domain) the form you
   would want upstreamed, or should a mathlib version use a partial/`Set`-domain or bundled
   formulation? (This decides whether the bridge lemma even has the same shape upstream.)

4. **Scope.** Is the p-adic logarithm theory (`ExtLog.lean` + `PadicExp.lean`) intended as a
   future mathlib contribution at all, or is it permanently project-internal scaffolding for
   the `L_p(θ,1)` computation? If permanently internal, this lemma drops out of mathlib
   consideration entirely (keep it as-is; the name is fine).

**Next action:** Run `/mathlibable PadicLFunctions.MeasureR.extLog` and
`/mathlibable PadicLFunctions.MeasureR.padicLog` (the parent definitions) first, then
re-run `/mathlibable extLog_eq_padicLog_of_norm_lt_one` to inherit/resolve. Likely outcomes:
  - parents `YES` + two-log design kept → this flips to `INHERITED-YES` (ship as the
    compatibility lemma alongside the two defs, in `Mathlib/NumberTheory/Padics/Log.lean`);
  - one-log modern idiom adopted → this is **absorbed** into the single log's characterizing
    lemma and is not a separate mathlib declaration;
  - theory kept project-internal → drop from mathlib consideration; current form/name is fine.

---

## Next step

Run `/mathlibable` on the two parent definitions `PadicLFunctions.MeasureR.extLog` and
`PadicLFunctions.MeasureR.padicLog` first (this lemma's verdict is inherited from theirs),
then re-run `/mathlibable extLog_eq_padicLog_of_norm_lt_one`. Separately, answer the
one-log-vs-two design question (Q2), which determines whether this lemma exists as a
standalone mathlib result at all.
