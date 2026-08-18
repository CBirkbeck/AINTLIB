# /mathlibable report — `Chebotarev.HasDirichletDensity`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. ChatGPT-math MCP was **down** (Codex `exec`
> command failed) — the literature channel used the documented WebSearch +
> WebFetch + nLab/Wikipedia/Encyclopedia-of-Math/lecture-note fallback. The Lean
> MCP search tools (loogle / leansearch) are not exposed in this environment and
> the local build is stale, so Phase 5 relies on direct `grep` over the vendored
> mathlib tree `.lake/packages/mathlib/` (commit `d90090f647`, toolchain
> `v4.31.0-rc2`), which is authoritative for "is it in mathlib".

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:               (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.HasDirichletDensity`:  resolved at
                            projects/Chebotarev/CebotarevDensity/Density.lean:64
- true qualified name:      Chebotarev.HasDirichletDensity
                            (namespace `Chebotarev` opened Density.lean:44; def at line 64)
                            — the parsed guess Chebotarev.HasDirichletDensity is CORRECT.
- kind:                     def  (a Prop-valued definition)
- has sorry:                no  (body is a total `Filter.Tendsto … ` term)
- module docstring summary: Dirichlet density of a set S of prime ideals of 𝓞 K,
                            δ(S) = lim_{s→1⁺} (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s});
                            plus limsup/liminf upper & lower variants.
```

Source (verbatim):

```lean
def HasDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) (𝓝 δ)
```

with `primeIdealZetaSum S s := ∑' 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`
(Density.lean:50). Context: `variable {K} [Field K] [NumberField K]`.

---

## Phase 1 — Statement (prose)

`Chebotarev.HasDirichletDensity S δ` is **the relation "the set `S` of prime ideals
of `𝓞 K` has Dirichlet density `δ`"**:

> Let `K` be a number field with ring of integers `𝓞 K`, and let `S` be a set of
> ideals of `𝓞 K`. Write `N𝔭 = Ideal.absNorm 𝔭` for the absolute norm. Form the
> partial Dirichlet series over the nonzero prime ideals lying in `S`,
> `P_S(s) = Σ_{𝔭 ∈ S, 𝔭 prime, 𝔭 ≠ 0} N𝔭^{-s}`, and the full one `P(s) = P_{univ}(s)`.
> Then `S` **has Dirichlet density** `δ ∈ ℝ` iff the ratio `P_S(s) / P(s)` tends to
> `δ` as `s` decreases to `1` from above:  `δ(S) = lim_{s → 1⁺} P_S(s)/P(s)`.

This is the standard "analytic / Dirichlet density of a set of primes", the size
measure underlying Dirichlet's theorem on primes in arithmetic progressions and
the Chebotarev density theorem. In this project it is the backbone notion whose
target value Chebotarev computes (`= |C|/|G|` for a Frobenius conjugacy-class
fibre).

**Variables / typeclasses (Lean side):**
- `{K : Type*} [Field K] [NumberField K]` — the number field. `NumberField`
  supplies finiteness of `𝓞 K / 𝔭` (so `absNorm` is meaningful) and the
  convergence of the prime-ideal zeta series for `Re s > 1`.
- `(S : Set (Ideal (𝓞 K)))` — the set of prime ideals tested.
- `(δ : ℝ)` — the candidate density value.

**Hypotheses (Lean side):** none — it is a definition (a `Prop`), not a theorem.

**Conclusion (math):** `S` has Dirichlet density `δ` (a property of `(S, δ)`).

**Conclusion (Lean):** `Prop`, namely
`Tendsto (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 δ)`.

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

```
Verdict: BIG
Reason: it introduces a NAMED mathematical structure/notion — the Dirichlet
density of a set of primes — as a new `def`. It is also a `## Main definitions`
entry of the file and the central notion of the whole Chebotarev project (the
quantity the main theorem computes). Named-after-a-mathematician concept
(Dirichlet). All three BIG triggers fire.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing.)
```

### One-line check (Phase 2b)

```
Body line count: 3 substantive lines (the `Tendsto`, the ratio function, the
                 two filters) — NOT a one-substantive-line body.
One-liner verdict: MULTI-LINE.
```

A `def` whose body is a `Tendsto` of a non-trivial ratio function across two
filters is multi-line; the one-liner negative-signal analysis does not apply. (Were
it judged a one-liner, exemption #3 "semantic intent / API name" would still
apply — 26 internal consumers depend on the stable name `HasDirichletDensity`;
see Phase 6.0.)

---

## Phase 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | Dirichlet density set of prime ideals number field, limit s→1                           | yes  | **ratio form**: `δ = lim_{s→1+} (Σ_{𝔭∈A} N𝔭^{-s})/(Σ_𝔭 N𝔭^{-s})` | Encyclopedia of Math + Wikipedia: ratio form is the **primary** definition; this is the project's exact form |
| 2  | WebSearch (general / log form)   | Dirichlet density vs natural/analytic density, comparison, standard                      | yes  | **log form**: `δ = lim_{s→1+} (Σ 1/p^s)/log(1/(s-1))` | Equivalent; "analytic density"; strictly more general than natural density |
| 3  | WebSearch (named-after / aliases)| upper/lower Dirichlet density limsup liminf, Serre Course in Arithmetic                  | yes  | upper = `limsup`, lower = `liminf` of the ratio **and** of the log-normalised form, **giving the same values** | Validates project's `HasUpper/LowerDirichletDensity`; the two normalisations agree |
| 4  | ChatGPT MCP                      | (5-part question on equivalence/generality/limsup convention)                            | n/a  | — | **MCP down** (Codex exec failed). Substituted by channels 5–10 per documented fallback. |
| 5  | Local references                 | grep `.mathlib-quality/references/`                                                      | n/a  | (no references dir; no `refs/Chebotarev/` store either) | dir absent — recorded n/a |
| 6  | nLab / nCatLab                   | nLab analytic density Dirichlet density primes                                           | part | "Dirichlet (analytic) density … easier than natural density; `lim (Σ_{p∈S} 1/p^z)/log(1/(z-1))`" | nLab `density` page indexed; concept is analytic-NT, not categorical → no dedicated nLab page; content matches #2 |
| 7  | Stacks Project                   | Stacks Dirichlet density Chebotarev prime ideals                                         | no   | — | **n/a** — analytic number theory, not an algebraic-geometry / commutative-algebra concept; Stacks has no Dirichlet-density entry (search returned only Wikipedia/Chebotarev notes) |
| 8  | MathOverflow / Math.SE           | (folded into #2/#3 generality queries)                                                   | yes  | confirms ratio ≡ log; natural ⊂ Dirichlet | Dirichlet density strictly more general than natural density; counterexample: leading-digit-1 primes |
| 9  | Lecture notes (Conrad / Kedlaya / MIT 18.785) | Conrad "Dirichlet density for global fields"; Kedlaya ANT ch.4; MIT 18.785 LN28  | yes  | global-field def; `Σ_p p^{-s} = -log(s-1)+O(1)`; Chebotarev fibre density `= |c|/|G|` | Kedlaya ANT ch.4 gives `limsup` ratio form explicitly; states number-field scope; Conrad title says "for **global fields**" |
| 10 | recent arXiv (≤5 yr)             | "Dirichlet density" global field function field Chebotarev formalization Lean            | yes  | Chebotarev for **global fields**: unramified Frobenius-class-`c` places have Dirichlet density `|c|/|G|` | arXiv 2203.12266 (Chebyshev bias, global fields), 2508.09480 (effective Chebotarev); **PrimeNumberTheoremPlus** project aims to formalize Chebotarev — but that is **not mathlib** |

### Literature summary (Phase 3)

```
Concept identified as: Dirichlet density (a.k.a. analytic density) of a set of
                       prime ideals of a number field / set of places of a global field.
Sources agree on the standard form: YES — two equivalent normalisations:
  (A) ratio:   lim_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})     ← THE PROJECT'S FORM
  (B) log:     lim_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s}) / log(1/(s-1))
  Equivalence: because Σ_𝔭 N𝔭^{-s} ~ log(1/(s-1)) (i.e. = -log(s-1)+O(1)) as s→1+
  (Wikipedia, Encyclopedia of Math, Kedlaya, MIT 18.785 LN all state this).
  The RATIO form (A) is presented as the PRIMARY definition by both Wikipedia and
  Encyclopedia of Mathematics; the log form is the computational equivalent.
Most general standard form: a set of (finite) places / nonzero primes of a GLOBAL
  field K, density = ratio (A) (equivalently (B)). Upper/lower via limsup/liminf,
  which agree across (A) and (B).
Generality dimensions where the literature varies:
  - base object: rational primes ⊂ prime ideals of a number field ⊂ places of a
    global field (number field OR function field F_q(t)). Most general = global field.
  - normalisation: ratio (A) vs log (B) — mathematically equivalent for existence
    and value; both are "standard"; (A) is the more common primary definition.
Disagreement with the literature: NONE. The project's def is normalisation (A),
  the primary textbook form, at the number-field generality.
```

A note on the project's **upper/lower convention** (Density.lean:69–92): the file
correctly flags that Sharifi's notes *invert* the "upper/lower" labels relative to
the standard `limsup = upper`. The project follows the **standard** convention
(`HasUpperDirichletDensity = limsup`), which channels 3 & 9 confirm is the
mathematically standard one. This is a correctness-relevant nicety but does not
bear on `HasDirichletDensity` (the two-sided `lim`) itself.

---

## Phase 4 — Generality analysis

### Generality analysis — `Chebotarev.HasDirichletDensity` (Phase 4a)

Literature-standard form (from Phase 3): the **ratio** `lim_{s→1⁺} P_S(s)/P(s)`,
for a set of nonzero primes / finite places of a **global field**.

| # | Parameter / hypothesis     | Current Lean form                    | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|--------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K]`          | K a number field                     | K a global field (number **or** function field) | **partially — NOT mechanically** | The function-field case uses a *different* size normalisation: places weighted by `q^{-s·deg}`, not `Ideal.absNorm^{-s}` over `𝓞 K`. Mathlib has **no `GlobalField` typeclass** (only a `FunctionField` abbrev) and `Ideal.absNorm` is the finite-residue-cardinality (number-field) norm. A genuine global-field def would need new infrastructure mathlib lacks; it is NOT a typeclass-weakening of this def. |
| 2 | normalisation = ratio (A)  | `P_S(s)/P_{univ}(s)` (ratio form)    | ratio (A) **or** log (B) `/log(1/(s-1))` | equivalent, not "weaker" | (A) and (B) define the same density; (A) is the primary textbook form. No generality is lost by (A); see Phase 4c for the idiom question. |
| 3 | `S : Set (Ideal (𝓞 K))`    | set of ideals (primality cut inside) | set of nonzero primes                    | NO (already maximally permissive) | Taking `S : Set (Ideal …)` and filtering `𝔭.IsPrime ∧ 𝔭 ≠ ⊥` inside `primeIdealZetaSum` is *more* flexible than requiring `S ⊆ {primes}`; lets callers feed arbitrary ideal sets. Good as is. |
| 4 | target `δ : ℝ`             | a real number; existence required    | real; existence required for `lim` to exist | NO | This is the `lim`-form; existence is intrinsic. The limsup/liminf relaxations are the *separate* `HasUpper/LowerDirichletDensity` defs, already present. |

### Generality verdict (Phase 4b)

```
The current form is: MAXIMALLY GENERAL (within the number-field setting, which is
                     the right and standard setting for an `Ideal.absNorm`-based density).
Number of weakening opportunities found: 0 mechanical ones.
  - The only "more general" target (global fields) is NOT a mechanical weakening:
    it requires a different normalisation and infrastructure mathlib does not have
    (no `GlobalField` typeclass; `absNorm` is the number-field norm). It is a
    separate, larger development — not a restatement of this def.
Proposed restatement: none (current number-field form is the right grain).
Cost of restatement: n/a (no restatement proposed).
```

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let X be a foo" preamble → typeclass/instance? | no | already a typeclass-driven def over `[NumberField K]` | — |
| 2  | sequences/metric where filters/topology generalise? | **already done** | the def **already** uses `Filter.Tendsto … (𝓝[>] 1) (𝓝 δ)` — the modern filter idiom, not an `ε`-`δ` or sequential `s_n ↓ 1` formulation | composes with all of mathlib's `Tendsto` / `nhdsWithin` API (squeeze, uniqueness, `Filter.Tendsto.div`) |
| 3  | construct an object where a universal-property class would characterise it? | no | density is a numeric limit, no universal property | — |
| 4  | set-with-closure-predicate → bundled substructure? | no | `S` is genuinely an arbitrary set of ideals; no substructure | — |
| 5  | vector-space/metric/field-specific → weaken typeclasses? | no | `[NumberField K]` is load-bearing (finite residue fields, zeta convergence) | — |
| 6  | 1-categorical → higher-categorical? | no | not categorical | — |
| 7  | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | no | the index `s : ℝ` is the real Dirichlet-series variable; intrinsic to the analytic notion | — |

```
### Modern-idiom verdict (Phase 4c)
Modern idiom available: NO new idiom to apply — the def is ALREADY in the
contemporary mathlib idiom (filter-based `Tendsto … (𝓝[>] 1) (𝓝 δ)` as a
`Prop`-valued relation, rather than a partial real-valued function requiring a
side existence hypothesis, and rather than a sequential `s_n ↓ 1` limit).
Reason this is not a (further) modernisation move: the only two anchors the
literature offers — the log-normalisation (B) and the global-field generalisation —
are respectively an equivalent restatement (no organisational gain; (A) is primary)
and a genuinely larger development needing absent infrastructure, not a reformulation.
```

The `Prop`-relation packaging (`HasDirichletDensity S δ`, mirroring mathlib's
`HasSum`, `HasDerivAt`, `HasFDerivAt`, `IsEquivalent`) is itself the idiomatic
mathlib choice over a junk-valued `dirichletDensity S : ℝ`: it sidesteps the
"value is junk when the limit doesn't exist" problem and lets uniqueness
(`Tendsto`-uniqueness, available since the target filter `𝓝[>] 1` is `NeBot`) be a
*theorem*, not baked into a `Classical.choice`. This matches the file's companion
`HasUpper/LowerDirichletDensity` (which use the always-defined `limsup`/`liminf`).

---

## Phase 4.5 — Diamond / defeq risk (kind = `def`)

`HasDirichletDensity` is a `Prop`-valued `def` (an abbreviation for a `Tendsto`
proposition). It defines **no** new data, instance, coercion, or algebraic
operation — it is essentially a named predicate. The diamond/defeq risk surface is
near-empty, but the six rows are filled for completeness.

### Diamond / defeq risk — `Chebotarev.HasDirichletDensity` (Phase 4.5a)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | Not an `instance`; introduces no typeclass and no instance-search path. |
| 2 | Reducibility leak            | none    | Not `@[reducible]`. Callers `rw [HasDirichletDensity]`/`simp only [HasDirichletDensity]` to unfold explicitly (Main.lean:204, Density.lean:99) — the seal is wanted, not a leak. |
| 3 | Non-canonical unfolding      | low     | It is definitionally a `Tendsto …`; `unfold`/`simp only [HasDirichletDensity]` exposes the ratio. No surprising `rfl`/`simp` behaviour beyond that one explicit unfold. |
| 4 | Instance priority collision  | none    | Not an `instance`; no priorities. |
| 5 | Universe-polymorphism issues | none    | `K : Type*` with `[Field K] [NumberField K]`; everything lands in `Prop`; no universe annotation forced. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`; the only coercion in the body is the standard `ℕ → ℝ` on `absNorm`, already canonical. |

### Risk verdict (Phase 4.5)

```
Overall risk: NONE
Top risks: none
Recommended mitigations: none required.
```

---

## Phase 5 — Mathlib search

Five-method search. Lean MCP tools (Loogle/LeanSearch/Lean-Finder) are not exposed
here and the build is stale; methods [A][B][C] are therefore run as `grep` over the
vendored mathlib source (authoritative for presence), and [E] as a name grep.
Both the **user's form** (number-field prime-ideal ratio) and the
**literature-standard general form** (any density-of-primes notion) were searched.

```
### Mathlib search-status: `Chebotarev.HasDirichletDensity`

[A] Lean-Finder       (unavailable)              n/a: MCP not exposed in this env
[B] Loogle            (unavailable)              n/a: MCP not exposed; substituted by [D] grep over type-shape
[C] LeanSearch        (unavailable)              n/a: MCP not exposed; substituted by [D] grep over concept terms
[D] Grep mathlib src  `DirichletDensity`, `Dirichlet.*density`, `density.*prime.*ideal`,
                      `def …Density` in NumberTheory/, `chebotarev`, `frobeniusClass`,
                      `GlobalField`         →  NO hits for ANY density-of-primes notion.
                      (All `\bdensity\b` hits are unrelated: probability density,
                      dense embeddings, Lebesgue density theorem, withDensity.)
[E] Name pattern      `HasDirichletDensity`, `dirichletDensity`  →  no hits.

Searched for both:
  - user's current form (number-field prime-ideal ratio): NOT in mathlib.
  - literature-standard general form (Dirichlet/analytic density of primes,
    global-field version, Chebotarev fibre density): NOT in mathlib.

Adjacent infrastructure that DOES exist (relevant for Phase 6):
  - `NumberField.dedekindZeta`, `NumberField.dedekindZeta_residue`,
    `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`
    (Mathlib/NumberTheory/NumberField/DedekindZeta.lean) — the ζ_K residue at s=1,
    i.e. the analytic ingredient NEAR the density, but NOT a density notion and NOT
    the per-prime partial-sum ratio.
  - mathlib has NO `GlobalField` typeclass (only `NumberTheory/FunctionField.lean`
    as a separate abbrev) and NO Chebotarev / Frobenius-density theorem.

Concluded: NOT in mathlib (all available methods exhausted, plus the
literature-standard general form). Mathlib has neither this def nor any
Dirichlet-/analytic-density-of-primes notion in any form.
```

---

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `Chebotarev.HasDirichletDensity` (Phase 6.0)

```
Internal use count: 26  (within the Chebotarev project, NOT counting the declaring
                    file Density.lean)
External-to-file callers: 4 distinct files
```

| Caller file:line                    | Usage pattern (one-line excerpt)                                              |
|-------------------------------------|------------------------------------------------------------------------------|
| CebotarevDensity/Abelian.lean:111   | `(hdens : ∀ i ∈ t, HasDirichletDensity (S i) c)` (hypothesis of a union lemma)|
| CebotarevDensity/Abelian.lean:874   | `have hUdens : HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c)`        |
| CebotarevDensity/Abelian.lean:1584  | `simp only [HasDirichletDensity, Nat.card_eq_fintype_card]` (unfold to ratio) |
| CebotarevDensity/Cyclotomic.lean:985| `HasDirichletDensity …` (conclusion of a cyclotomic density result)          |
| CebotarevDensity/Main.lean:73       | `HasDirichletDensity …` (statement of the main Chebotarev density theorem)    |
| CebotarevDensity/Main.lean:114      | `(h : HasDirichletDensity S δ) (hδ : 0 < δ)` (infinitude-from-positive-density)|
| CebotarevDensity/Main.lean:202–204  | `HasDirichletDensity (T \ S) 0 … ; rw [HasDirichletDensity] at hS …`          |
| (+ ~19 further occurrences across Abelian.lean / Main.lean / Cyclotomic.lean)    | density-statement conclusions, hypotheses, and explicit `rw`/`simp` unfolds   |

```
Inline-derivation grep (was the ratio-Tendsto re-spelled elsewhere without using
`HasDirichletDensity`?):  (none) — every site goes through the named def; the
`Tendsto … (𝓝[>] 1) (𝓝 δ)` shape never appears open-coded in a consumer.
```

**Signal (per the call-sites table):** K = 26 internal uses across 4 files, **no**
inline re-derivation anywhere → this is a real, load-bearing API; consumers depend
on the stable name. Strong **YES-\*** lean.

### Composition check (Phase 6a)

```
Can `Chebotarev.HasDirichletDensity` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Tendsto (P_S / P_univ) (𝓝[>] 1) (𝓝 δ)` — this is what the def IS. The
  body is built from `Filter.Tendsto`, `nhdsWithin`, `tsum`, `Ideal.absNorm`,
  `Real.rpow` — all mathlib primitives. But assembling them is *spelling a
  definition*, not *deriving a statement*: there is no mathlib lemma whose
  conclusion is this `Tendsto`, because the very notion "Dirichlet density" is
  absent from mathlib. A `def` cannot be "composed away" the way a lemma can —
  the question for a def is whether mathlib already names this concept (Phase 5:
  no) and whether it is the right concept (Phases 3–4: yes).
  Result: not applicable in the lemma sense — this is a definitional anchor, not a
  derivable proposition.

Conclusion: NOT-COMPOSABLE (as a "use mathlib at the call site instead" move).
  Mathlib has the *raw* `Tendsto`/`tsum`/`absNorm` constructors, but no named
  Dirichlet-density concept; inlining the bare `Tendsto …` at all 26 call sites
  (instead of the named def) would DESTROY the API, not compose it. The named def
  is exactly what the 26 consumers need. The `dedekindZeta_residue` infra is
  *adjacent* (it powers the eventual proof that `P_univ ~ log(1/(s-1))`) but is not
  this definition and does not compose to it in ≤3 calls.
```

---

## Phase 7 — Verdict

```
## Verdict: `Chebotarev.HasDirichletDensity`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): Dirichlet (analytic) density of a set of primes is a
  canonical, named concept (Dirichlet); the RATIO form `lim_{s→1+} P_S/P` is the
  PRIMARY textbook definition (Wikipedia, Encyclopedia of Math) and is EXACTLY the
  project's form; ≥9 channels concur, no disagreement.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the number-field setting
  (the correct setting for an `Ideal.absNorm`-based density). 0 mechanical
  weakenings. The lone "more general" anchor (global fields) is a separate larger
  development needing infrastructure mathlib lacks, NOT a restatement. Phase 4c: the
  def is ALREADY in the modern filter-`Tendsto`/`Prop`-relation idiom.
- Mathlib search (Phase 5): NOT in mathlib — no Dirichlet-/analytic-density-of-primes
  notion in ANY form; no Chebotarev/Frobenius density; no `GlobalField` typeclass.
- Composition check (Phase 6): NOT-COMPOSABLE — a definitional anchor used by 26
  consumers with zero inline re-derivation; bare `Tendsto` constructors exist but
  do not constitute a named concept, and inlining would destroy the API.
- Diamond/defeq risk (Phase 4.5): NONE (Prop-valued predicate, no instance/coercion/data).

**Rationale:**

Dirichlet density is one of the foundational size-measures of analytic number
theory — the notion underlying Dirichlet's theorem on primes in arithmetic
progressions and the Chebotarev density theorem. Mathlib today has the Dedekind
zeta function and its residue at `s = 1` (`NumberField.dedekindZeta_residue`,
`tendsto_sub_one_mul_dedekindZeta_nhdsGT`) but **no notion of the density of a set
of primes at all** — the exhaustive grep finds zero hits under either the
number-field form or any general form. That is the concrete, nameable gap: a
library that has the class number formula but cannot *state* "this set of primes
has density δ" is missing the vocabulary that every downstream equidistribution
result (Chebotarev, Dirichlet-AP density `1/φ(b)`, splitting-density, Sato–Tate-style
statements) is phrased in. This project's def fills exactly that gap, in the
primary textbook normalisation (the ratio form), packaged as a `Prop`-valued
relation `HasDirichletDensity S δ` in deliberate analogy with `HasSum`/`HasDerivAt`
— the idiomatic mathlib choice that makes value-uniqueness a theorem rather than a
`Classical.choice` artifact, and that the file extends consistently to
`HasUpper/LowerDirichletDensity` via always-defined `limsup`/`liminf`.

On generality: the number-field restriction is correct, not a deficiency. The
function-field ("global field") case is genuinely different at the level of the
size weight (degree-based `q^{-s·deg}` rather than `Ideal.absNorm^{-s}`), mathlib
has no `GlobalField` typeclass to hang a unified def on, and `Ideal.absNorm` is
intrinsically the number-field (finite-residue-cardinality) norm. So there is no
mechanical weakening to perform first — this is the maximally-general form
expressible with present mathlib infrastructure, and the verdict is YES-add-as-is
rather than YES-but-generalise-first.

**WHY add it (refactor-actionable):**
- New content mathlib is missing: the Dirichlet/analytic **density of a set of
  prime ideals** of a number field — there is no such def in mathlib (Phase 5
  exhaustive grep: zero hits, both forms). The specific gap: mathlib has
  `NumberField.dedekindZeta` + its `s=1` residue but no way to *state* a
  density-of-primes result; every equidistribution theorem (Chebotarev,
  Dirichlet-AP, splitting density) needs this vocabulary and currently cannot be
  stated in mathlib at all.
- How it composes with mathlib: as a `Filter.Tendsto … (𝓝[>] 1) (𝓝 δ)` predicate it
  immediately inherits the full `Tendsto`/`nhdsWithin` calculus — uniqueness
  (`tendsto_nhds_unique`, since `𝓝[>] 1` is `NeBot`), `Filter.Tendsto.div`,
  squeeze theorems, and the `IsEquivalent`/`dedekindZeta_residue` API for proving
  the denominator asymptotic. The companion limsup/liminf variants slot into
  mathlib's `limsup`/`liminf` order API.

Proposed mathlib location:   Mathlib/NumberTheory/NumberField/DirichletDensity.lean
                             (sits naturally beside DedekindZeta.lean, which supplies
                             the s=1 analytic input; namespace `NumberField` rather
                             than the project's `Chebotarev`).
Proposed PR title:           "feat(NumberTheory): Dirichlet density of a set of prime ideals"
PR grouping:                 ship `HasDirichletDensity` together with
                             `primeIdealZetaSum`, `HasUpperDirichletDensity`,
                             `HasLowerDirichletDensity`, and the basic API lemmas
                             from Density.lean (empty/finite/monotone/union/disjoint,
                             `infinite_of_hasDirichletDensity_pos`) as ONE coherent
                             "Dirichlet density" PR — the def is not useful to
                             mathlib without that surrounding lemma layer. The
                             upper/lower convention note (vs Sharifi's inverted
                             labels) should be preserved in the docstring.
Pre-PR checklist before opening:
  - [ ] /generalise Chebotarev.HasDirichletDensity — confirm no easy further
        weakening (expected: none beyond the global-field non-starter; sanity-check
        whether `[NumberField K]` could be spelt via a weaker mixin once the
        zeta-convergence lemmas it needs are isolated).
  - [ ] /cleanup CebotarevDensity/Density.lean HasDirichletDensity — full audit +
        diff gates on the whole density-API block to mathlib style.
  - [ ] Pick a reviewer from Mathlib/NumberTheory/NumberField/ recent commits
        (DedekindZeta / L-series area).
  - [ ] Decide naming: `NumberField.HasDirichletDensity` vs a `setOf`-based name;
        confirm `primeIdealZetaSum` naming against mathlib's `LSeries` conventions.
```

### Phase 7 gate self-check

- YES-add-as-is requires: Phase 3 lit table ≥3 channels ✓ (10 rows); Phase 4
  generality = MAXIMALLY GENERAL ✓; Phase 4.5 risk NONE ✓; Phase 5 no hit ✓;
  Phase 6 NOT-COMPOSABLE ✓; not a one-liner ✓; bucket-specific WHY names a
  concrete gap (mathlib has ζ_K residue but no density-of-primes notion) ✓.
- Phase 4b was MAXIMALLY GENERAL (not STRICTLY NARROWER) → YES-add-as-is permitted,
  YES-but-generalise-first not forced. ✓
- Phase 4c found no *new* modern idiom to apply (the def already is the modern
  idiom) → not pushed to YES-but-generalise-first MODERN-IDIOM. ✓
- Cost was NOT cited as a downgrade reason. The global-field non-generalisation is
  on infrastructure-absence + different-normalisation grounds (a genuine
  mathematical difference), not "too expensive". ✓

---

## Phase 8 — Next step

Run, in order, before any mathlib PR:
1. `/generalise Chebotarev.HasDirichletDensity` — confirm no further weakening
   (expected: none; the global-field form is a separate development, not a
   weakening).
2. `/cleanup CebotarevDensity/Density.lean` over the whole Dirichlet-density API
   block.
3. Open one grouped `feat(NumberTheory)` PR adding `primeIdealZetaSum`,
   `HasDirichletDensity`, `HasUpperDirichletDensity`, `HasLowerDirichletDensity`
   and their basic lemmas to `Mathlib/NumberTheory/NumberField/DirichletDensity.lean`
   (namespace `NumberField`), preserving the upper/lower-convention docstring note.
```
```
