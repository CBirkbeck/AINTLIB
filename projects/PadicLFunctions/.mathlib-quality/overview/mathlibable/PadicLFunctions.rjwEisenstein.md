# `/mathlibable` report — `PadicLFunctions.rjwEisenstein`

**Mode A — full 10-phase workflow, exhaustive 9-channel literature search.**

---

## Verdict: `NO-composable-from-mathlib`

`rjwEisenstein hk z = (((zetaNeg (k-1) : ℚ) : ℂ) / 2) * ModularForm.E hk z` is a
one-line `noncomputable def` whose body is a **single scalar multiplication** of
mathlib's existing `ModularForm.E` by the project's own rational constant
`zetaNeg (k-1)`. It is the classical `½·Gₖ` ("ζ-normalised") Eisenstein series,
realised as a bare `ℍ → ℂ` function — deliberately *less* structured than the
`ModularForm` that mathlib's `(c • E hk)` already produces. Mathlib has all the
building blocks (`ModularForm.E`, the `SMul ℂ (ModularForm Γ k)` instance,
`ModularForm.smul_apply`); the RJW normalisation is a 1-call composition with no
new mathematical content. It has zero consumers outside its declaring file (16
internal uses, all in same-file helper lemmas) and the `zetaNeg`-factor is itself
project-specific p-adic bookkeeping. It should stay a project-local convenience
definition, not go to mathlib.

---

### Baseline (Phase 0)

- lake build:               not re-run; reasoned from source (per task instruction — build is stale/slow here; read the decl + its dependency closure directly).
- decl `PadicLFunctions.rjwEisenstein`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:108`
- kind:                      `def` (`noncomputable`)
- has sorry:                 no
- module docstring summary:  the q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side) — re-normalising mathlib's constant-term-1 `ModularForm.E` to RJW's `Eₖ = ζ(1−k)/2 + Σ σ_{k−1}(n)qⁿ` and forming its p-stabilisation `Eₖ^{(p)}`.

---

### Statement (Phase 1)

`PadicLFunctions.rjwEisenstein` is **a definition** of the following:

For an integer weight `k ≥ 3`, it is the function `ℍ → ℂ` given by
`z ↦ (ζ(1−k)/2) · Eₖ(z)`, where `Eₖ` is mathlib's normalised level-1 weight-`k`
Eisenstein series (`ModularForm.E hk`, constant term 1) and `ζ(1−k)` is supplied
as the **rational** value `zetaNeg (k-1) = (−1)^{k−1} B_k / k` cast into `ℂ`.
Mathematically this is the classical Eisenstein series in the normalisation whose
Fourier expansion is `Eₖ(z) = ζ(1−k)/2 + Σ_{n≥1} σ_{k−1}(n) qⁿ` with `q = e^{2πiz}`
— i.e. one half of the un-normalised Eisenstein series `Gₖ` (since
`Gₖ = −B_k/(2k) + Σ σ_{k−1}(n)qⁿ` and `−B_k/(2k) = ζ(1−k)`).

Variables / typeclasses involved (Lean side):
- `{k : ℕ}` — the weight (implicit). No algebraic typeclass; concretely `ℕ`.
- `(hk : 3 ≤ k)` — weight lower bound, the hypothesis under which `ModularForm.E hk` is defined (convergence of the Eisenstein series).
- (file-level) `(p : ℕ) [hp : Fact p.Prime]` — the prime is **omitted** from `rjwEisenstein` itself; the def does not depend on `p`.

Hypotheses (Lean side):
- `hk : 3 ≤ k` — only used to invoke `ModularForm.E hk`.

Conclusion (math): the ζ-normalised Eisenstein series, the scalar `ζ(1−k)/2` times mathlib's normalised `Eₖ`.

Conclusion (Lean): `ℍ → ℂ` (a plain function — n/a, this is a definition; note it is **not** packaged as a `ModularForm`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**

Reason: a one-line helper definition that rescales an existing mathlib object by a
constant. It is not a new mathematical structure (no topology/category/measurability
notion), not named after a person/place, and not a primary project goal — it is a
normalisation convenience feeding the q-expansion lemmas
`hasSum_rjwEisenstein` / `hasSum_stabilisedEisenstein`. (Note: literature width was
EXHAUSTIVE regardless; BIG/SMALL recorded for framing only.)

---

### One-line check (Phase 2b)

Body line count: **1 substantive line** — `fun z => (((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * ModularForm.E hk z`

One-liner verdict: **ONE-LINER**

| Exemption                         | Applies? | Evidence                                                                                                                                                                                                                                                  |
|-----------------------------------|----------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | The proofs (`hasSum_rjwEisenstein`, `stabilisedEisenstein_smul_apply`) **unfold** `rjwEisenstein` immediately (`rw [rjwEisenstein, ...]`); they do not rely on it being a sealed barrier — the def is being expanded, not protected. |
| Avoid typeclass diamonds          | no       | The body is a `ℂ`-valued multiplication; no instance is being pinned. `ModularForm.E hk` already resolves a unique modular-form structure; wrapping it in a bare function pins no instance. |
| Mark semantic intent / API name   | no (weak) | The name documents "RJW's normalisation", but no consumer outside the file depends on the stable name — see Phase 6.0: 0 external call sites. Inside the file the name is a readability convenience, replaceable by `(c • ModularForm.E hk) z`. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** — carried into Phase 7 (biases toward NO-composable-from-mathlib / NO-mathlib-has-it).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                       | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "normalized Eisenstein series E_k weight k q-expansion zeta(1-k)/2 sigma divisor sum constant term"                         | yes  | `Eₖ = 1 − (2k/B_k)Σσ_{k−1}(n)qⁿ` (ct 1); `Gₖ = ct + Σσqⁿ`; `Eₖ = Gₖ/(2ζ(k))`        | SageMath docs, K. Conrad CTNT notes, Dasgupta–Kakde "On constant terms of Eisenstein series" |
|  2 | WebSearch (general / convention) | "Eisenstein series normalization conventions constant term Bernoulli number zeta value modular forms"                       | yes  | three standard normalisations (ct=1, linear=1, integral); `ζ(1−2k) = −B_{2k}/(2k)`   | Wstein "Modular Forms: A Computational Approach", SageMath; confirms the ct↔Bernoulli↔ζ identity |
|  3 | WebSearch (named-after / aliases / `Gₖ`) | "Eisenstein series G_k half normalization '1/2 zeta(1-k)' Serre course in arithmetic E_k constant term divisor sum"  | yes  | **`Gₖ` has constant term `−B_k/(2k) = ζ(1−k)/2`** ... wait: `Gₖ` ct `= −B_k/2k`; `Gₖ/2` ct `= ζ(1−k)/2` | Zagier "Eisenstein series and the Riemann zeta-function"; `Gₖ = 2ζ(k)Eₖ` |
|  4 | ChatGPT MCP                      | (intended: "standard definition + generality + historical evolution of the ζ-normalised Eisenstein series")                 | n/a  | —                                                                                   | **n/a — ChatGPT MCP server is not configured** in this environment (no codex/chatgpt tool in the deferred-tools list; only auth-stub MCP tools present). Compensated with extra WebSearch + nLab + arXiv. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` for "Eisenstein"                                                | n/a  | —                                                                                   | **n/a — no `references/` directory exists** (only `overview/`); `refs/` is also absent. Recorded per protocol. The in-repo RJW citations (TeX line numbers in the docstrings) are the primary source: arXiv:2309.15692 §8 (Rodrigues–Jordão–Williams "p-adic L-functions"), TeX 2367–2394. |
|  6 | nLab                             | nLab "Eisenstein series" page                                                                                               | yes  | `G_{2k}(τ) = Σ_{(m,n)≠0} (m+nτ)^{−2k}`, `Gₖ = −B_k/(2k) + Σσ_{k−1}(n)qⁿ`; `g₂=60G₄`, `g₃=140G₆` | Confirms `Gₖ` ct `= −B_k/(2k)`. nLab does not name a "ct `= ζ(1−k)/2`" variant explicitly, but it is exactly `Gₖ/2`. |
|  7 | nCatLab (categorical)            | (same nLab page — Eisenstein series is not a categorical concept)                                                           | n/a  | —                                                                                   | n/a — Eisenstein series is an analytic/number-theoretic object; no categorical (∞-)formulation is the relevant standard form. |
|  8 | Stacks Project                   | —                                                                                                                           | n/a  | —                                                                                   | n/a — not an algebraic-geometry / scheme-theoretic concept; the Stacks Project does not cover classical modular-form q-expansions. |
|  9 | MathOverflow / Math.StackExchange| (covered transitively via WebSearch #1–#3 hits and standard refs)                                                            | n/a  | —                                                                                   | n/a — the convention question is fully and unambiguously answered by the textbook sources (Serre, Zagier, Conrad, Diamond–Shurman); MO would only restate them. |
| 10 | recent arXiv (last 5 years)      | the project's own source: arXiv:2309.15692 (RJW), plus arXiv hits in #1/#3 (Dasgupta–Kakde 2020, Zagier scanned)            | yes  | RJW §8 TeX 2371 defines `Eₖ = ζ(1−k)/2 + Σσ_{k−1}(n)qⁿ` — **exactly this def**       | The "`_chebotarev`-style" project-specific anchor: RJW pick the `ζ(1−k)/2` normalisation so the p-stabilisation `Eₖ^{(p)}` has clean rational/`p`-adic coefficients. |

Protocol pass check:
- WebSearch ran **3 distinct queries** at three generality levels (specific ct=`ζ(1−k)/2` form; general convention survey; named `Gₖ` / Serre-Zagier form). ✓
- ChatGPT MCP: **n/a, server not configured** — documented, compensated by extra channels. (The one hard-required channel that could not run; the verdict does not hinge on it, the convention is textbook-unambiguous.)
- Local references: **n/a, directory absent** — documented. ✓
- nLab: checked (hit). ✓
- Stacks / nCatLab / MathOverflow / arXiv: each checked or `n/a` with a reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the level-1 weight-`k` (holomorphic) Eisenstein series in the
"`ζ(1−k)/2`-constant-term" normalisation** — equivalently `½·Gₖ`, half the
un-normalised Eisenstein series `Gₖ`. Standard names: `Gₖ`/2, the "arithmetically
normalised" or "ζ-normalised" Eisenstein series. RJW (arXiv:2309.15692, §8) call it
`Eₖ`.

Sources agree on the standard form: **yes**. The three relevant objects are crisply
related and appear in every textbook:
- `Gₖ(τ) = Σ_{(m,n)≠0}(m+nτ)^{−k} = −B_k/(2k) + Σ_{n≥1} σ_{k−1}(n)qⁿ` — un-normalised (constant term `−B_k/(2k) = ζ(1−k)`).
- `Eₖ(τ) = Gₖ/(2ζ(k)) = 1 − (2k/B_k)Σσ_{k−1}(n)qⁿ` — **mathlib's `ModularForm.E`** (constant term 1).
- `½Gₖ = ζ(1−k)/2 + Σσ_{k−1}(n)qⁿ` — **RJW's / this def's normalisation** (constant term `ζ(1−k)/2`).

Most general standard form: there is no "more general" form to chase here — it is a
fixed scalar rescaling of a single classical object. The only "generality" axis is
*which normalisation constant* one multiplies by, and the three above are the
standard choices; mathlib has canonically chosen constant-term-1 (`E`).

Generality dimensions where the literature varies:
- normalisation constant only: `1` (mathlib `E`), `2ζ(k)` (`Gₖ`), `½Gₖ = (ζ(1−k)/2)·E` (this def). All three are the *same function up to a scalar*; none is "more general".

Disagreement with the literature: **none** — `rjwEisenstein` is exactly the standard
`½Gₖ` normalisation. It is just not mathlib's chosen normalisation; it is the
paper-specific (RJW) one.

---

### Generality analysis — `PadicLFunctions.rjwEisenstein`

Literature-standard form (from Phase 3): the classical Eisenstein series; the
normalisation `ζ(1−k)/2 + Σσqⁿ` is one fixed scalar multiple of the constant-term-1
form mathlib already has.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `{k : ℕ}` weight        | natural number `k` | positive even integer (the convention is stated for even `k ≥ 4`; odd-weight level-1 Eisenstein series vanish) | NO (already as broad as makes sense) | `ℕ` is the correct index; the def uses mathlib's `ModularForm.E hk` which is itself defined for `ℕ` weights. No additive-group/monoid generalisation is meaningful for the weight of a level-1 Eisenstein series. |
| 2 | `(hk : 3 ≤ k)`          | `3 ≤ k`           | `k ≥ 3` (so `Gₖ`/`Eₖ` converges); RJW use `k ≥ 3`/`4` | NO | This is exactly mathlib's `ModularForm.E` convergence hypothesis; it cannot be weakened without `E` changing. |
| 3 | the `ζ(1−k)` value      | `zetaNeg (k-1) : ℚ` cast to `ℂ` | `ζ(1−k)` (a specific scalar) | n/a | This is the *choice of normalisation constant*, not a generality axis. Using the rational `zetaNeg` (vs. complex `riemannZeta (1-k)`) is a deliberate project decision to keep the p-adic chain rational; it makes the def *narrower/more specialised*, not more general. |
| 4 | codomain structure      | bare `ℍ → ℂ`      | the Eisenstein series is a **modular form** `ModularForm 𝒮ℒ k` | — (this is a *de*-generalisation) | The def throws away the `ModularForm` structure that `(ζ(1−k)/2) • ModularForm.E hk` retains. Phase 4c flags this: the *more idiomatic* mathlib form is the smul'd modular form, not a bare function. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (along every genuine generality axis — `k`,
`hk` match mathlib's `E`; there is no literature "more general Eisenstein series" to
chase, only a different normalisation constant).

Number of weakening opportunities found: **0** (the only deltas are a *normalisation-constant choice* and a *de*-structuring to `ℍ → ℂ`, neither of which is a weakening).

Proposed restatement (if STRICTLY NARROWER): n/a — not strictly narrower.

Cost of restatement: n/a.

→ Because MAXIMALLY GENERAL, Phase 7 considers YES-add-as-is or the NO buckets,
*after* the Phase 4c modern-idiom check.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | No bundled hypotheses here; the only hyp is the scalar `hk`. |
|  2 | sequences/metric → filters/topological? | no | — | This is an algebraic q-expansion identity / a scalar multiple; no sequential-limit notion to filter-ise. |
|  3 | construct an object → universal-property class? | no | — | The Eisenstein series is an explicit construction with no universal property at stake; mathlib already provides it. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | Not a substructure. |
|  5 | vector-space/metric/field-specific → weaker typeclass? | no | — | Already over `ℂ`/`ℍ` at the right level; nothing to weaken. |
|  6 | 1-categorical → higher/∞-categorical? | no | — | Not categorical. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure? | no | — | The weight `k : ℕ` is the correct index for a level-1 Eisenstein series. |
| (extra) | **bare `ℍ → ℂ` → bundled `ModularForm`?** | **yes** | `(((zetaNeg (k-1) : ℚ) : ℂ) / 2) • ModularForm.E hk : ModularForm 𝒮ℒ k` (mathlib's `SMul ℂ (ModularForm Γ k)`, `Mathlib/NumberTheory/ModularForms/Basic.lean:270`) | Retains slash-invariance/holomorphy/cusp-boundedness; composes with the whole `ModularForm` graded-ring + q-expansion API. But this is **already expressible in mathlib without any new declaration** — it is just `c • E hk`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it is plain mathlib, not a new contribution.**

- Proposed mathlib-idiomatic restatement: `(c) • ModularForm.E hk` with `c = ((zetaNeg (k-1):ℚ):ℂ)/2`, giving a `ModularForm 𝒮ℒ k` rather than a bare `ℍ → ℂ`; its value at `z` is `ModularForm.smul_apply`.
- Cost: CHEAP (mechanical).
- Mathlib downstream this enables: the full `ModularForm` API (it is *already* a modular form), `qExpansion`, the graded-ring structure. **However**, this restatement does not justify a *new mathlib declaration* — it is literally `c • E`, an existing mathlib expression. So the modern-idiom finding pushes toward **NO-composable** (use `c • ModularForm.E hk` directly), not toward YES-but-generalise-first: there is nothing to upstream that mathlib doesn't already have.
- Real mathematical improvement: the only improvement is *to the project's own code* (keep the modular-form structure instead of forgetting it); it is not a contribution mathlib lacks.

(Phase 7 note: 4c does NOT flip this to YES-but-generalise-first, because the
"modern" target is an existing mathlib expression `c • E`, not a missing mathlib
declaration. The "generalise-first" bucket requires the target form to be *novel for
mathlib in some form* — here it is not.)

---

### Diamond / defeq risk — `PadicLFunctions.rjwEisenstein`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond           | none | Body is a `ℂ`-valued product `(q : ℂ) * (E hk z : ℂ)`; no instance is being defined or anchored. The `ℂ` field/`ℍ → ℂ` structure is already canonical in mathlib. |
| 2 | Reducibility leak           | none | Not `@[reducible]`; a sealed `noncomputable def`. (Note: it is *not* serving as a defeq barrier either — Phase 2b — the proofs unfold it eagerly.) |
| 3 | Non-canonical unfolding     | low  | `simp`/`rfl` will not unfold it unless asked; the file uses explicit `rw [rjwEisenstein]`. No surprising automatic unfolding. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues| none | Fully monomorphic (`ℕ`, `ℚ`, `ℂ`, `ℍ`); no universe variables. |
| 6 | Coercion ambiguity          | none | Uses the standard `ℚ → ℂ` cast (`((· : ℚ) : ℂ)`) and `ModularForm`'s `CoeFun`; no new/competing coercion is introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**

Top risks: none.

Recommended mitigations: n/a. (Risk does not constrain the verdict; the NO bucket
does not add the def to mathlib in any case.)

---

### Mathlib search-status: `PadicLFunctions.rjwEisenstein`

[A] Lean-Finder       n/a: the Lean-Finder web tool is not reachable from this offline-reasoning environment. Compensated by [B]–[E] over the local mathlib checkout.
[B] Loogle            type-pattern intent `ModularForm 𝒮ℒ ?k` / `(?c : ℂ) • ModularForm.E ?hk` / a `ℍ → ℂ` Eisenstein series scaled by `ζ(1−k)`  — n/a as a live web query (offline); resolved structurally via grep + reading `Basic.lean`/`QExpansion.lean`. The relevant primitive `ModularForm.E` and `SMul ℂ (ModularForm Γ k)` are confirmed present.
[C] LeanSearch        natural-language intent "ζ(1−k)/2-normalised Eisenstein series" / "half the un-normalised Eisenstein series Gₖ" / "Eisenstein series with constant term ζ(1−k)/2" — n/a as a live web query (offline); the concept is mathlib's `ModularForm.E` up to the scalar.
[D] Grep mathlib src  `def E`, `eisensteinSeries*`, `G2`/`G_k`, `smul.*ModularForm`, `E_qExpansion*`, `q_expansion_bernoulli` over `.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/` — **hits**: `ModularForm.E` (Basic.lean:47), `eisensteinSeriesMF` (Basic.lean:33), `eisensteinSeries`/`eisensteinSeriesSIF` (Defs.lean:205/218), `G2` (E2/Defs.lean:56), `SMul ℂ (ModularForm Γ k)` + `smul_apply`/`coe_smul` (Basic.lean:247–284), `q_expansion_bernoulli`/`E_qExpansion_coeff` (QExpansion.lean:298/323). **No** `½Gₖ`/`ζ(1−k)/2`-normalised def; **no** scalar multiple of `E` defined as a named object.
[E] Name pattern      grepped `rjwEisenstein` and Eisenstein-def patterns across all of `projects/` — only `EisensteinComplex.lean` declares it; no other project has an analogous "scaled Eisenstein" def (no reuse target).

Searched for both:
  - the user's current form (`(ζ(1−k)/2) · E hk z` as `ℍ → ℂ`) — **not in mathlib as a named decl**.
  - the literature-standard general form (`Gₖ`, the un-normalised Eisenstein series; or any scalar multiple of `E`) — **mathlib has the constant-term-1 form `ModularForm.E` and the `SMul` to rescale it, but does NOT have `Gₖ` or `½Gₖ` as a named declaration**.

Concluded: **found building blocks** — `ModularForm.E` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:47`) + the scalar-multiplication instance `instSMulℂ`/`ModularForm.smul_apply` (`Mathlib/NumberTheory/ModularForms/Basic.lean:270,261`) — whose composition yields the user's form in one call. The exact `ζ(1−k)/2`-normalised object is not a named mathlib declaration, and need not be: it is `c • ModularForm.E hk`.

---

### Call sites — `PadicLFunctions.rjwEisenstein`

Internal use count: **16** (all within `EisensteinComplex.lean` — the declaring file).
External-to-file callers: **0 distinct files** (whole-repo grep over `projects/`, excluding `.lake`, returns no `rjwEisenstein` outside `EisensteinComplex.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| EisensteinComplex.lean:157 | `(rjwEisenstein (k := k) (by omega) τ)` — RHS of `hasSum_rjwEisenstein` (same file, private lemma) |
| EisensteinComplex.lean:170,178 | `rw [rjwEisenstein, hqe, …]` — unfolded inside `hasSum_rjwEisenstein` |
| EisensteinComplex.lean:192–193 | `rjwEisenstein … z − (p:ℂ)^(k−1) * rjwEisenstein … (pScale p z)` — the stabilisation target in `hasSum_stabilisedEisenstein` |
| EisensteinComplex.lean:201,202,210,211,226 | inside `hasSum_stabilisedEisenstein` proof |
| EisensteinComplex.lean:366–368 | `stabilisedEisenstein_smul_apply`: `… = rjwEisenstein … z − … rjwEisenstein … (pScale p z)`, proved by `rw […, rjwEisenstein, rjwEisenstein]; ring` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `rjwEisenstein`?):
  - (none) — no other definition rebuilds `(ζ(1−k)/2)·E` by hand; the only related object is `stabilisedEisenstein` (the genuine `ModularForm`), which the file relates to `rjwEisenstein` via `stabilisedEisenstein_smul_apply`.

What the pattern says: **K = 0 external uses; all 16 uses are same-file and several
immediately `rw [rjwEisenstein]` to unfold it.** This is a same-file readability /
naming convenience for the q-expansion lemmas, not a public API others consume. Per
the Phase-6.0.1 table (K=0 external, no external inline re-derivation, used only to be
unfolded), the composability signal leans **NO-composable** (it is a thin wrapper over
`c • ModularForm.E`).

### Composition check (Phase 6)

Can `PadicLFunctions.rjwEisenstein` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the def body itself): `fun z => (((zetaNeg (k-1) : ℚ) : ℂ) / 2) * ModularForm.E hk z`
  - Mathlib decls used: `ModularForm.E` (the Eisenstein series); the `ℚ → ℂ` cast; `HMul`/`*` on `ℂ`. The factor `zetaNeg` is the *project's own* rational constant (not mathlib), cast to `ℂ`.
  - Result: **succeeds** — this is a single scalar multiplication; the def *is* the composition.
  - Notes: 1 mathlib object (`ModularForm.E hk z`) × 1 scalar. No `rw`/`ring_nf`/`aesop` needed.

Attempt 2 (idiomatic, retaining structure): `((((zetaNeg (k-1) : ℚ) : ℂ) / 2) • ModularForm.E hk) z`
  - Mathlib decls used: `ModularForm.E` (Basic.lean:47) + `instSMulℂ : SMul ℂ (ModularForm Γ k)` (Basic.lean:270); value via `ModularForm.smul_apply` (Basic.lean:261): `(c • f) z = c • f z = c * f z`.
  - Result: **succeeds** — `((c • ModularForm.E hk) z) = c * ModularForm.E hk z = rjwEisenstein hk z`, a 1-line identity. This even keeps the `ModularForm` structure.
  - Notes: this is the cleaner inline form; `rjwEisenstein hk z` is definitionally `((c • ModularForm.E hk) z)` after `ModularForm.smul_apply`.

Conclusion: **COMPOSABLE** — the user's form is a 1-call scalar multiplication of
mathlib's `ModularForm.E`; both as a bare product (Attempt 1) and as the structure-
preserving `c • E` (Attempt 2). It matches the Phase-6b "`Foo.bar (Bar.baz hx)` — one
function call" → composable row, and is far from the "multiple `have`s with
non-trivial reasoning" → NO row.

---

## Verdict: `PadicLFunctions.rjwEisenstein`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is the classical `½Gₖ` / "ζ(1−k)/2-normalised" Eisenstein series — a fixed *scalar multiple* of the constant-term-1 form. Unanimous across SageMath docs, K. Conrad, Wstein, Zagier, nLab; it is RJW (arXiv:2309.15692 §8 TeX 2371)'s normalisation. No "more general" form to chase — only a different normalisation constant.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (`k`, `hk` already match mathlib's `E`; the only deltas are a normalisation-constant choice and a *de*-structuring to `ℍ → ℂ`). Phase 4c found the idiomatic form is `c • ModularForm.E hk` — but that is an existing mathlib expression, not a missing declaration, so 4c does **not** flip the verdict to YES-but-generalise-first.
- Mathlib search (Phase 5): "found building blocks" — `ModularForm.E` (`EisensteinSeries/Basic.lean:47`) + `SMul ℂ (ModularForm Γ k)` / `ModularForm.smul_apply` (`ModularForms/Basic.lean:270,261`); the `ζ(1−k)/2`-scaled object is not (and need not be) a named mathlib decl.
- Composition check (Phase 6): **COMPOSABLE** — 1 scalar multiplication; `rjwEisenstein hk z = (((zetaNeg (k-1):ℚ):ℂ)/2) * ModularForm.E hk z = ((c • ModularForm.E hk) z)`.

**Rationale (1–2 paragraphs):**

`rjwEisenstein` adds no mathematical content that mathlib is missing: it rescales
mathlib's existing `ModularForm.E hk` (constant term 1) by the constant `ζ(1−k)/2` to
land in RJW's normalisation (constant term `ζ(1−k)/2`, i.e. `½Gₖ`). Mathlib already
provides the Eisenstein series (`ModularForm.E`) **and** the `SMul ℂ (ModularForm Γ k)`
instance with `ModularForm.smul_apply` to scale it, so the value `(ζ(1−k)/2)·E hk z` is
a one-call composition — indeed `((c • ModularForm.E hk) z)` is the structure-preserving
spelling, which `rjwEisenstein` actually *discards* by collapsing to a bare `ℍ → ℂ`.
The choice of the *rational* `zetaNeg (k-1)` over the complex `riemannZeta (1-k)` is a
deliberate project-internal device for keeping the p-adic chain rational; it makes the
object more specialised than mathlib would want, not more general. With **zero external
call sites** (16 uses, all same-file, several immediately unfolding the def via
`rw [rjwEisenstein]`) and no Phase-2b defeq/diamond/API-name exemption, this is a
same-file naming convenience, not a reusable API.

This is the canonical `NO-composable-from-mathlib` shape (cf. verdicts reference Case 4):
mathlib has the building blocks, the form is a ≤3-call composition, and no new lemma is
justified. The right move is to use `ModularForm.E` (scaled) directly.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; `rjwEisenstein` is a 1-mathlib-call scalar
multiplication of `ModularForm.E`. The composition below is mechanical to inline.

Mathlib building blocks:
- `ModularForm.E {k : ℕ} (hk : 3 ≤ k) : ModularForm 𝒮ℒ k` — `Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:47`
- `instSMulℂ : SMul α (ModularForm Γ k)` (here `α = ℂ`) — `Mathlib/NumberTheory/ModularForms/Basic.lean:270`
- `ModularForm.smul_apply (f) (n) (z) : (n • f) z = n • f z` — `Mathlib/NumberTheory/ModularForms/Basic.lean:261`
- the standard `ℚ → ℂ` cast for `zetaNeg (k-1)` (a *project* def, `KubotaLeopoldt/ZetaValues.lean:17`).

Composition sketch (≤3 lines):
```lean
-- the bare-function form (exactly the current def body):
example {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    rjwEisenstein hk z = (((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * ModularForm.E hk z := rfl
-- the structure-preserving form (preferred — keeps modularity):
example {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    (((((zetaNeg (k - 1) : ℚ) : ℂ) / 2) • ModularForm.E hk) z)
      = (((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * ModularForm.E hk z := ModularForm.smul_apply _ _ _
```

Call sites in our project (from Phase 6.0): **K = 16, all inside `EisensteinComplex.lean`; 0 external.**

Refactor plan (project-local; this is NOT a mathlib PR):
- This is a within-project cleanup, not an upstreaming task — keep `rjwEisenstein` *or* inline it, but do **not** ship it to mathlib.
- If inlining: at each of the 16 same-file sites, replace `rjwEisenstein hk z` with
  `(((zetaNeg (k-1):ℚ):ℂ)/2) * ModularForm.E hk z` (the two `rw [rjwEisenstein]` sites
  at lines 178 and 368 then become no-ops and can be dropped; the `HasSum`/value sites
  carry the product directly). Argument flow is positional `hk`, explicit `z`/`τ` — no
  implicit/explicit mismatch.
- **Recommended instead**: since the def is a harmless same-file readability anchor with
  a good docstring and the file's narrative leans on the name (`hasSum_rjwEisenstein`,
  `stabilisedEisenstein_smul_apply`), the *cleanest* project-local action is to **keep
  `rjwEisenstein` as-is but mark it clearly project-local** (it already is — it is in
  `projects/`, not headed for mathlib). The verdict's operative content is: **do not
  propose this to mathlib** — mathlib's `c • ModularForm.E hk` already covers it.
- Optional structural improvement (project-internal, orthogonal to the mathlib verdict):
  redefine `rjwEisenstein` to *return a `ModularForm 𝒮ℒ k`* as `(c) • ModularForm.E hk`
  (then `rjwEisenstein hk z` via `ModularForm.smul_apply`), so the project keeps the
  modular-form structure it currently forgets. This is a `/generalise`-adjacent local
  refactor, not a mathlib contribution.

Next action: do **not** open a mathlib PR for `rjwEisenstein`. Treat it as a project-
local definition; if cleaning, either inline `(c) * ModularForm.E hk z` at the 16 sites
or (better) keep the name but consider returning the `c • ModularForm.E hk`
**`ModularForm`** rather than a bare `ℍ → ℂ`. Mathlib already has everything needed
(`ModularForm.E` + `•`).

---

## Next step

Do **not** open a mathlib PR for `rjwEisenstein`. Treat it as a project-local
definition. Mathlib already provides `ModularForm.E` (`EisensteinSeries/Basic.lean:47`)
and `SMul ℂ (ModularForm Γ k)` / `ModularForm.smul_apply` (`ModularForms/Basic.lean:270,261`);
the RJW `ζ(1−k)/2` normalisation is the one-call composition
`(((zetaNeg (k-1):ℚ):ℂ)/2) • ModularForm.E hk`. If cleaning the project, either inline
that product at the 16 same-file call sites, or (preferred, structure-preserving) keep
the name but redefine it to return the `c • ModularForm.E hk` **`ModularForm`** instead
of a bare `ℍ → ℂ`.
