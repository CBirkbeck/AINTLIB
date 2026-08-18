# `/mathlibable` report — `PadicLFunctions.unitsTwist_moment`

Single-declaration Mode-A assessment, full 10-phase workflow with the exhaustive
nine-channel literature search.

---

### Baseline (Phase 0)

- lake build:               not re-run (stale/slow per task note); **reasoned from source** — the
  declaration and its full dependency chain were read directly from the `.lean` files. Phase-0
  fallback per the skill.
- decl `PadicLFunctions.unitsTwist_moment`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:141`
- kind:                      theorem
- has sorry:                 no (whole file is sorry-free; `grep` confirms)
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8)" — the Kubota–Leopoldt
  pseudo-measure interpolates the constant coefficients of the p-stabilised Eisenstein series
  `E_k^{(p)}`; the file builds the Λ-adic Eisenstein family `𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`.

The substrate types/defs were read in full: `PadicMeasure` (`Measure/Basic.lean:52`), `unitsCmul`
+ `unitsCmul_apply` (`KubotaLeopoldt/ZetaP.lean:64,69`), `unitsPowCM` (`Measure/PseudoMeasure.lean:650`),
`unitsTwist` (`EisensteinFamily.lean:115`), and the private helper the theorem aliases,
`unitsCmul_powCM_one_moment` (`EisensteinFamily.lean:105`).

---

### Statement (Phase 1)

`PadicLFunctions.unitsTwist_moment` is a theorem stating the following:

Let `p` be a prime and let `Λ(ℤ_p^×) := PadicMeasure p ℤ_[p]ˣ` be the space of `ℤ_p`-valued
measures on `ℤ_p^×` — defined (RJW Def. 3.6) as the `ℤ_p`-linear dual
`C(ℤ_p^×, ℤ_p) →ₗ[ℤ_p] ℤ_p`, i.e. the Iwasawa algebra realised as the continuous dual. Let
`τ = unitsTwist` be the **x-twist**: the ring automorphism of `Λ(ℤ_p^×)` given by
`(τμ)(f) = μ(x·f)` (multiplication of the measure by the coordinate function `x : u ↦ u`; on Dirac
measures `[g] ↦ g·[g]`). Write `∫ x^k dμ := μ(unitsPowCM p k)` for the `k`-th power moment, where
`unitsPowCM p k : C(ℤ_p^×, ℤ_p)` is the test function `u ↦ (u : ℤ_p)^k`.

Then **the x-twist shifts the power-moment index up by one**:
`∫ x^k d(τμ) = ∫ x^{k+1} dμ`   for every measure `μ` and every `k ∈ ℕ`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `μ : PadicMeasure p ℤ_[p]ˣ` — a `ℤ_p`-valued measure on `ℤ_p^×` (element of the Iwasawa algebra).
- `k : ℕ` — the moment index.

Hypotheses (Lean side): none beyond the parameters.

Conclusion (math): integrating `x^k` against the x-twisted measure equals integrating `x^{k+1}`
against the original — multiplication-by-`x` reindexes power moments by `+1`.

Conclusion (Lean):
`unitsTwist p μ (PadicMeasure.unitsPowCM p k) = μ (PadicMeasure.unitsPowCM p (k + 1))`.

**Proof body (load-bearing for the verdict):** the entire proof is
```lean
  unitsCmul_powCM_one_moment p μ k
```
i.e. `unitsTwist_moment` is an exported, un-`private` restatement of the private helper
`unitsCmul_powCM_one_moment` (line 105), whose own proof is two `rw`s:
`unitsCmul_apply` (unfold `(τμ)(g) = μ(x·g)`, definitionally) then `unitsPowCM_one_mul_unitsPowCM`
(the pointwise identity `x · x^k = x^{k+1}`). The mathematical content is the one-line computation
`∫ x·x^k dμ = ∫ x^{k+1} dμ`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/corollary — a one-line exported alias (`:= unitsCmul_powCM_one_moment p μ k`) of a
private lemma, computing one moment of the project's own `unitsTwist` automorphism. It is neither a
named main result, nor a new structure, nor a person/place-named theorem. (It supports the §8 main
result `eisensteinFamily_interpolation`, but is itself plumbing.)

(Note: literature width was EXHAUSTIVE regardless — all nine channels run below.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`unitsCmul_powCM_one_moment p μ k`).
One-liner verdict: n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. The Phase-2b def
exemption table does not apply to theorems. Recorded for narrative: this is a **one-line glue
theorem** (term-mode alias of a private lemma), which biases Phase 7 toward a NO/BORDERLINE
disposition unless a strong API reason surfaces.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Iwasawa algebra measure multiplication by x moment Mellin transform shift p-adic L-function" | partial | framework standard; **no** named "moment-shift under ×x" lemma | top hits: RJW/J. Rodrigues Jacinto–C. Williams *Intro to p-adic L-functions* (the source the project formalizes); de Shalit *Mahler bases*; Loeffler–Zerbes style notes. All describe measures = continuous dual + Amice/Mahler transform; none states this particular shift as a result. |
| 2 | WebSearch (general form / Amice) | "p-adic measure x^k moment multiplication by x twist Amice transform power moment" | partial | Amice transform `A_μ(t)=Σ tⁿ∫(y choose n)dμ`; convolution ↔ power-series product | de Shalit and *p-adic L-functions for GL(n)* (arXiv:1503.01283): Amice transform is a norm-preserving Banach iso; multiplication-by-`x` on measures corresponds to the operator `(1+t)d/dt` on Amice transforms — the *binomial-moment* shift, not the *power-moment* `x^k↦x^{k+1}` index shift used here. No standalone lemma in the user's form. |
| 3 | WebSearch (named-after / aliases: Mellin, multiplication operator) | "distribution multiplication operator shifts power moments Mellin transform shift one rule" | partial | classical Mellin: `t^a`-multiplication ⇄ `s`-shift; Mellin = moment generator | the archimedean analogue (Mellin transform of `ℝ→ℂ`) is standard and *is* in mathlib (`mellin_cpow_smul`, `MellinTransform.lean:100`), but that is a different object (real integral transform), not the `ℤ_p`-valued functional here. |
| 4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of the multiplication-by-x moment-shift for p-adic measures") | **n/a** | — | **No ChatGPT/Codex MCP tool is configured in this environment** (only OAuth-stub MCP servers — Asana/Atlassian/etc. — are present). Recorded n/a with reason; compensated by extra WebSearch depth (rows 1–3, 10) + direct source read (row 5 attempt). |
| 5 | Local references | `grep .mathlib-quality/references/` + `refs/` symlink | n/a | — | **No references directory present.** `projects/PadicLFunctions/.mathlib-quality/` contains only `overview/`; `refs/` symlink absent in this checkout (PDFs are local-only per CLAUDE.md and not on `main`). Attempted to fetch the RJW notes online (row 10) — PDF was un-OCR-able by WebFetch. |
| 6 | nLab | "Iwasawa algebra / p-adic measures continuous dual / Mahler transform" | yes (framework) | Iwasawa algebra `R[[ℤ_p]] = lim R[ℤ/pⁿ]` = `R`-valued measures = continuous dual of `C(ℤ_p,R)`; Mahler transform `A_xA_y=A_{x+y}` | nLab confirms the *framework* (measures = continuous dual; transform respects convolution) but has no entry for the ×x power-moment-shift as a named fact. |
| 7 | nCatLab (categorical) | (same as 6) | n/a | — | Not a categorical concept — it is an elementary functional-evaluation identity. No higher-categorical content to look up. |
| 8 | Stacks Project | (alg-geom?) | n/a | — | Not an algebraic-geometry concept; the Stacks Project has no p-adic-measure / Iwasawa-algebra analytic chapter. |
| 9 | MathOverflow / Math.StackExchange | "p-adic measure twist by x shifts moments Iwasawa algebra Eisenstein family lambda-adic" | partial | Eisenstein-measure constructions (Serre, Katz, Hida, Eischen) routinely twist measures and read off moments | confirms twisting-measures-and-reading-moments is bread-and-butter Iwasawa theory, done *inline* per construction; surfaced no standalone "×x shifts the power moment by one" lemma. |
| 10 | recent arXiv (last ~5 yr) | "p-adic moments of L-functions" (arXiv:2507.01836); "An introduction to Eisenstein measures" (arXiv:2101.01879); Williams Warwick lecture notes | yes (framework) | Eisenstein measures interpolate L-values via moments; constant terms give Iwasawa-algebra elements | the moment ↔ interpolation philosophy is ubiquitous and recent, but the elementary index-shift is an inline computation, never isolated as a result. WebFetch of the RJW PDF failed (binary/compressed). |

Protocol pass check:
- WebSearch ran **3** distinct queries at different generality levels (rows 1–3) + a 4th at the
  named/recent level (row 10). ✓
- ChatGPT MCP: **not available** in this environment → recorded n/a with reason, compensated. ✓
- Local references: checked → absent → n/a with reason. ✓
- nLab: checked (row 6). ✓
- Stacks / nCatLab / MathOverflow / arXiv: each checked or n/a-with-reason (rows 7–10). ✓

### Literature summary (Phase 3)

Concept identified as: the **power-moment behaviour of an Iwasawa-algebra measure under
multiplication by the coordinate function `x`** (RJW §8 "x-twist" of the Eisenstein family).
Equivalently: the operator "multiply a measure on `ℤ_p^×` by `x`" reindexes power moments
`∫x^k ↦ ∫x^{k+1}`.

Sources agree on the standard form: **yes on the framework, no on this specific lemma.** Universally,
across nLab, de Shalit, the GL(n) notes, and the RJW notes, the Iwasawa algebra is the continuous
dual `C(ℤ_p, ℤ_p)→ℤ_p`, multiplication-by-a-function on measures is the standard dual operation, and
moments interpolate L-values. But the *specific* statement `∫x^k d(x·μ)=∫x^{k+1}dμ` is **not** a
named or numbered result anywhere — it is the trivial unfolding `∫x·x^k dμ=∫x^{k+1}dμ`, performed
inline whenever needed.

Most general standard form (literature): for a measure `μ` on a profinite abelian group `G` (here
`ℤ_p^×`) and a continuous "weight" character/function `χ`, multiplying `μ` by `χ` and pairing against
another character/monomial `ψ` gives `(χ·μ)(ψ)=μ(χψ)` — pure bilinearity of the dual pairing. The
"+1 index shift" is the case `χ = x`, `ψ = x^k`, using `x·x^k = x^{k+1}`.

Generality dimensions where the literature varies:
- coefficient ring: `ℤ_p` here; literature also does `𝒪_L`, `ℂ_p`, general Banach coefficients.
- base group: `ℤ_p^×` here; literature also `ℤ_p`, `ℤ_p^n`, `𝒪_F^×`, Galois groups `Γ`.
- the "multiplier": coordinate `x` here; literature multiplies by arbitrary continuous characters
  (Tate-twist style), of which `x` is the simplest non-trivial case.

Disagreement with the literature: **none.** The Lean statement is a faithful, very special instance
of the standard dual-pairing identity; it is just stated for the project's bespoke `unitsPowCM`/
`unitsCmul` API.

If the literature returned nothing as a *named* result, that is itself the signal (per the skill): the
declaration is too elementary / too project-specific to be a recognised theorem. Phase 7 weighs this.

---

### Generality analysis — `PadicLFunctions.unitsTwist_moment`

Literature-standard form (from Phase 3): the dual-pairing identity `(χ·μ)(ψ) = μ(χψ)`, specialised
to a coordinate-function multiplier and monomial test functions.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `μ : PadicMeasure p ℤ_[p]ˣ` | `ℤ_p`-measure on `ℤ_p^×` | measure on a profinite abelian group, general Banach coeffs | yes (in principle) | content is pure bilinearity of the dual pairing; nothing uses `ℤ_p^×` or `ℤ_p` specifically. But "weakening" presupposes a general `PadicMeasure`/Iwasawa-algebra framework in mathlib — which **does not exist** (Phase 5). |
| 2 | the multiplier `unitsPowCM p 1` (`x`) | the coordinate function `x` | an arbitrary continuous character/multiplier `χ` | yes | the proof only needs `x·x^k=x^{k+1}`; the genuinely general lemma is `(χ·μ)(f)=μ(χ·f)` — which is **already** the project's `unitsCmul_apply` (`:= rfl`). `unitsTwist_moment` is the `χ=x`, `f=x^k` instance plus the monomial product. |
| 3 | test function `unitsPowCM p k` (`x^k`) | monomial `x^k` | arbitrary `f ∈ C(ℤ_p^×, ℤ_p)` | yes | same as #2 — the monomial-specific part is exactly the `x·x^k=x^{k+1}` step. |
| 4 | `k : ℕ` | natural exponent | — | n/a | the index lives in `ℕ`; nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `χ=x`, `f=x^k` specialisation of
the bilinear dual-pairing identity).
Number of weakening opportunities found: 3 (rows 1–3) — but with a crucial caveat: the genuinely
general statement (`(χ·μ)(f)=μ(χ·f)`) is **already present in the project as `unitsCmul_apply` and
holds by `rfl`**, and the further generalisation to an abstract Iwasawa-algebra framework is blocked
because mathlib has no such framework (Phase 5).

Proposed restatement (only meaningful relative to the existing project API): there is nothing to
"restate" — the general form is `unitsCmul_apply` (definitional). `unitsTwist_moment` is best
understood as: `unitsCmul_apply` (general) + `unitsPowCM_one_mul_unitsPowCM` (the `x·x^k=x^{k+1}`
monomial fact). Both already exist.

Cost of restatement: n/a — the more general form already exists in-project; no re-proof is needed.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the only "structure" (`PadicMeasure`) is already an `abbrev` for a `LinearMap`; nothing to bundle. |
| 2 | sequences/metric → filters/topology? | no | — | no limits/convergence here; it is an algebraic functional identity. |
| 3 | explicit construction → universal-property class? | no | — | no construction; it is an evaluation identity. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no substructure involved. |
| 5 | vector-space/field-specific → module/(semi)ring weakening? | partial (already done) | the content already lives at the `LinearMap`/dual-pairing level | the genuinely general form is the project's `unitsCmul_apply` (`(χ·μ)(f)=μ(χf)`, `rfl`); `unitsTwist_moment` adds only the monomial computation. No further modernisation flips the verdict. |
| 6 | 1-categorical → higher/∞-categorical? | no | — | not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general monoid/group? | partial | `k : ℕ` could be `χ` an arbitrary character (row 2 above) | but that "modern" form is again just `unitsCmul_apply`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (nothing that flips the verdict). The "more idiomatic" form is the
bilinear dual-pairing identity, which the project *already* states as `unitsCmul_apply` (definitional).
`unitsTwist_moment` is the monomial specialisation; modernising it does not produce new mathematical
organisation — it just re-derives the existing `unitsCmul_apply`. One-line reason: the only abstraction
move (multiplier `x` → arbitrary character) collapses to a lemma the project already has by `rfl`.

---

### Diamond / defeq risk — `PadicLFunctions.unitsTwist_moment`

n/a — declaration kind is `theorem`. Phase 4.5 is skipped for theorems/lemmas (no definitional
equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.unitsTwist_moment`

[A] Lean-Finder       (no Lean-Finder MCP configured) — n/a: tool absent in this environment.
[B] Loogle            type pattern `PadicMeasure _ _ → C(_,_) → _` and `(_ * _) (_) = _ (_ )`  — n/a: the head symbols (`PadicMeasure`, `unitsTwist`, `unitsPowCM`, `unitsCmul`) are **project-private**; Loogle indexes mathlib only and cannot match them. The abstract shape `dualPairing (χ • μ) f = μ (χ * f)` has no mathlib analogue over `C(X, ℤ_p)`-functionals.
[C] LeanSearch        natural-language: "multiplying a p-adic measure by x shifts the power moment"; "measure on units, integral of x^k against x-twist" — no hits (no p-adic-measure / Iwasawa-algebra API in mathlib).
[D] Grep mathlib src  `grep -rn "PadicMeasure|unitsTwist|unitsCmul|unitsPowCM"` over `.lake/packages/mathlib/Mathlib/` → **zero matches**. `grep` for `Iwasawa|pseudo.?measure|Kubota|Leopoldt` → **zero matches**. The entire RJW p-adic-measure framework is absent from mathlib (pin `d90090f647ca`, toolchain `v4.31.0-rc2`).
[E] Name pattern      `*_moment`, `*Twist*`, `*Cmul*` in mathlib → only unrelated `Probability.Moments.*` (real/complex MGF moments of probability measures) and `MellinTransform` lemmas (`mellin_cpow_smul`, `mellin_comp_mul_left`, …) — different objects.

Searched for both:
  - the user's current form (`unitsTwist p μ (unitsPowCM p k) = μ (unitsPowCM p (k+1))`) — no hit;
  - the literature-standard form (bilinear `(χ·μ)(f)=μ(χf)`) over a `ℤ_p`-valued continuous dual — no
    hit (the closest mathlib has is `WeakDual` / `ContinuousLinearMap` pairings, none with the
    measure/Iwasawa semantics; and the Mellin-transform shift lemmas, which are a different transform).

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form).
The decisive finding is structural: **mathlib has none of the substrate** — no `PadicMeasure`, no
Iwasawa algebra as a continuous dual, no `unitsPowCM` test functions, no `unitsCmul`/`unitsTwist`.
There is therefore nothing to specialise from and no building block to compose with at the
measure-theoretic level.

---

### Call sites — `PadicLFunctions.unitsTwist_moment`

Internal use count: **1** (within the project, NOT counting the declaring line).
External-to-file callers: **0 distinct files** (the theorem is used only inside its own file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:274` | `rw [hνeq, LinearMap.smul_apply, smul_eq_mul, unitsTwist_moment, Nat.sub_add_cancel …]` — inside `twistedZetaHalf_moments`, to turn `νb(x^{k})` from `(c·τνb)(x^{k-1})` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `unitsTwist_moment`?):
  - Yes — the **private** helper `unitsCmul_powCM_one_moment` (line 105) is the actual content; it is
    also invoked directly elsewhere in the `map_mul'` field of the `unitsTwist` def
    (`EisensteinFamily.lean:131–133`, three calls), bypassing the public alias. So the underlying
    identity is used ~4× in-file, but the *public theorem* `unitsTwist_moment` only once.

Supplementary scope fact: the def the theorem is *about*, `unitsTwist`, occurs **only** in
`EisensteinFamily.lean` (grep across all projects, `.lake` excluded) — it is never imported or used by
any other file or downstream library. Call-sites signal: **K = 1 internal use of a one-line glue
theorem over a project-private, single-file def** → leans toward NO/BORDERLINE per the Phase-6
signal table.

### Composition check (Phase 6)

Can `unitsTwist_moment` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `unitsCmul_apply` ▸ then a monomial rewrite.
  - Mathlib decls used: **none available** — `unitsCmul_apply`, `unitsPowCM`, `unitsTwist` are all
    project-private; mathlib has no `PadicMeasure` API.
  - Result: **fails as a mathlib composition** — there is no mathlib decl to chain. (As a *project*
    composition it is trivially `unitsCmul_apply` + `unitsPowCM_one_mul_unitsPowCM`, i.e. exactly the
    body of the private `unitsCmul_powCM_one_moment` — but those are project lemmas, not mathlib.)

Attempt 2 (mathlib angle via the abstract dual pairing): could one phrase it with
`ContinuousLinearMap`/`WeakDual` mathlib pairings and a `mul`-rewrite?
  - Mathlib decls used: `LinearMap.comp`, `LinearMap.mulLeft` exist generically, but assembling the
    measure semantics (`(τμ)(f)=μ(x·f)` with `x·x^k=x^{k+1}`) requires first *defining* the whole
    `PadicMeasure`/`unitsCmul`/`unitsPowCM` layer. That is framework construction, not a ≤3-call glue.
  - Result: **fails** — it is a proof-over-a-new-framework, not a composition of existing mathlib
    primitives.

Conclusion: **NOT-COMPOSABLE from mathlib.** (It *is* a 2-step composition from *project* primitives,
but those primitives are not in mathlib, so the `NO-composable-from-mathlib` bucket — which means
"inline mathlib calls at the call site" — does not apply.)

---

## Verdict: `PadicLFunctions.unitsTwist_moment`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *framework* (Iwasawa algebra = measures = continuous dual;
  Amice/Mahler transform; moments interpolating L-values) is fully standard across nLab, de Shalit,
  the GL(n) notes, and the RJW source; but the *specific* statement `∫x^k d(x·μ)=∫x^{k+1}dμ` appears
  **nowhere as a named/numbered result** — it is the trivial inline identity `∫x·x^k dμ=∫x^{k+1}dμ`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — it is the `χ=x`, `f=x^k`
  specialisation of the bilinear pairing `(χ·μ)(f)=μ(χf)`, whose general form is *already* the
  project's `unitsCmul_apply` (`rfl`). Modern-idiom check (4c): no verdict-flipping modernisation.
- Mathlib search (Phase 5): **not in mathlib**, and decisively, **none of the substrate is in
  mathlib** (no `PadicMeasure`, no Iwasawa algebra as a continuous dual, no `unitsPowCM`/`unitsCmul`).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (composable only from project-private
  lemmas, which is not the `NO-composable` bucket).

**Rationale (1–2 paragraphs):**

This is a one-line glue theorem (`:= unitsCmul_powCM_one_moment p μ k`) — an exported, un-`private`
alias of a private helper — about the project's own ring automorphism `unitsTwist` of the project's
own object `PadicMeasure p ℤ_[p]ˣ`. Its mathematical content is the trivial reindexing
`∫ x·x^k dμ = ∫ x^{k+1} dμ`. None of the four NO/YES buckets fits cleanly. It is **not**
`NO-mathlib-has-it` (Phase 5: mathlib has nothing). It is **not** `NO-composable-from-mathlib` (Phase 6:
mathlib has no `PadicMeasure` building blocks to inline; the composition exists only from
project-private lemmas). It is **not** `YES-add-as-is` (Phase 4b: STRICTLY NARROWER, and the
verdict gate forbids YES-add-as-is on a STRICTLY-NARROWER form; moreover the general form already
exists in-project as `unitsCmul_apply`). And it is **not** cleanly `YES-but-generalise-first`: the
"generalised" target (`(χ·μ)(f)=μ(χf)`) is not a new contribution — it is `unitsCmul_apply`,
definitional — so "generalise then PR" would propose upstreaming a lemma the project proves by `rfl`,
and only *after* an entire `PadicMeasure`/Iwasawa-algebra framework had been built in mathlib.

The honest blocker is a **framework-scope judgment the skill cannot make alone**: `unitsTwist_moment`
rides entirely on the RJW continuous-dual `PadicMeasure` substrate, which mathlib does not have. The
real mathlibability question is not about this lemma but about whether that whole substrate
(p-adic measures as `C(X,ℤ_p)→ℤ_p`, the Iwasawa algebra, the `unitsCmul`/`unitsTwist` operations)
should be upstreamed — and if so, in what form (very likely a general `χ·μ` multiplication plus an
abstract moment/Amice-transform API, of which this `+1` shift would be a `simp`-level corollary, not a
standalone theorem). That is a deliberate project/mathlib-design call. Layered on top is a smaller
taste call: even granting the framework, a single-call one-line alias of a private lemma is borderline
as a standalone mathlib declaration versus folding it into the general `unitsCmul_apply` API. Both are
human decisions, so the verdict is BORDERLINE with the questions spelled out below.

**Refactor-actionable bar — numbered questions for the human (≤5):**

1. **Framework first.** Do you intend to upstream the RJW p-adic-measure substrate to mathlib at all
   — `PadicMeasure X := C(X, ℤ_p) →ₗ[ℤ_p] ℤ_p`, the Iwasawa-algebra/convolution structure, and the
   `unitsCmul`/`unitsPowCM`/`unitsTwist` API? (If **no**, `unitsTwist_moment` is project-local
   bookkeeping and drops out of mathlib consideration entirely — keep it as-is in the project.)

2. **Right grain.** If yes to (1): should the *general* multiplication-by-a-function identity
   `(χ·μ)(f) = μ(χ·f)` (currently the project's `unitsCmul_apply`, which holds by `rfl`) be the
   mathlib API surface, with the `+1` power-moment shift `∫x^k d(x·μ)=∫x^{k+1}dμ` demoted to an inline
   `simp`/one-liner at use sites — rather than shipping `unitsTwist_moment` as its own named theorem?

3. **Bundling.** If a moment/Amice-transform API is upstreamed, would you prefer the moment-shift
   expressed at the level of the transform (the operator `(1+t)d/dt` on Amice transforms, per de Shalit
   / the GL(n) notes) so it composes with a future mathlib Amice-transform isomorphism, instead of the
   bespoke `unitsPowCM`-indexed form used here?

4. **Coefficients/base.** If upstreaming the framework, at what generality — `ℤ_p`-valued on `ℤ_p^×`
   only (current), or general `𝒪_L`-valued on a profinite abelian group `G`? (The lemma's proof is
   pure dual-pairing bilinearity, so it survives the general form unchanged; the question is the
   intended scope of the mathlib contribution.)

**Next action:** the user answers the questions; re-run `/mathlibable PadicLFunctions.unitsTwist_moment`
to resolve the verdict. Likely resolutions:
  - **No to Q1** → drop from mathlib consideration; keep project-local (most likely: the whole RJW
    development is research-stage and not yet a mathlib target).
  - **Yes to Q1, yes to Q2** → `unitsTwist_moment` itself becomes `NO-composable-from-mathlib` *relative
    to the future framework* (a one-liner over the upstreamed `unitsCmul_apply`); the real
    contribution is the framework + the general `χ·μ` API, assessed separately.
  - **Yes to Q1, no to Q2** (ship the named shift too) → `YES-but-generalise-first`, restated against
    the general `χ`/coefficients of Q4, sequenced *after* the framework PR.

---

## Next step

The user answers the four numbered questions above; re-run
`/mathlibable PadicLFunctions.unitsTwist_moment` to resolve the verdict. The decisive question is Q1
(is the underlying `PadicMeasure`/Iwasawa-algebra framework a mathlib target at all?) — every concrete
disposition of this glue lemma hangs on it, because mathlib currently has none of the substrate the
lemma is stated over.
