# /mathlibable report — `Chebotarev.HasLowerDirichletDensity`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. Environment notes: the local Lean build is
> **stale** and the Lean MCP search tools (loogle / leansearch / Lean-Finder) are
> **not exposed** in this environment, so Phase 5 relies on direct `grep` over the
> vendored mathlib tree `.lake/packages/mathlib/` (commit `d90090f647`, toolchain
> `leanprover/lean4:v4.31.0-rc2`), which is authoritative for "is it in mathlib".
> The ChatGPT-math MCP was treated as down (documented WebSearch + nLab/Wikipedia/
> Encyclopedia-of-Math / lecture-note fallback used instead). This decl is the
> `liminf` sibling of `Chebotarev.HasDirichletDensity` (the two-sided `lim`) and
> `Chebotarev.HasUpperDirichletDensity` (the `limsup`); the companion
> `HasDirichletDensity.md` report in this directory did the shared heavy literature
> lifting and its findings are cross-referenced and independently re-confirmed here
> for the lower/liminf form.

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:               (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.HasLowerDirichletDensity`:  resolved at
                            projects/Chebotarev/CebotarevDensity/Density.lean:89
- true qualified name:      Chebotarev.HasLowerDirichletDensity
                            (namespace `Chebotarev` opened Density.lean:44; def at line 89)
                            — the parsed guess Chebotarev.HasLowerDirichletDensity is CORRECT.
- kind:                     def  (a Prop-valued definition)
- has sorry:                no  (body is a total `Filter.liminf … = δ` proposition)
- module docstring summary: Dirichlet density of a set S of prime ideals of 𝓞 K,
                            δ(S) = lim_{s→1⁺} (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s});
                            plus limsup (upper) & liminf (lower) variants used in the
                            Chebotarev sandwich argument.
```

Source (verbatim, Density.lean:87–92):

```lean
/-- Lower Dirichlet density (`liminf` of the ratio). See `HasUpperDirichletDensity` for the
convention note: this matches Sharifi's `δ_inf` notation despite Sharifi's labelling inversion. -/
def HasLowerDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  liminf
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ
```

with `primeIdealZetaSum S s := ∑' 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`
(Density.lean:50). Context: `variable {K : Type*} [Field K] [NumberField K]
{S : Set (Ideal (𝓞 K))} {δ : ℝ}` (Density.lean:46).

Companion defs in the same file: `HasDirichletDensity` (line 64, the two-sided `Tendsto … = δ`),
`HasUpperDirichletDensity` (line 82, the `limsup … = δ`). The three form the standard
upper / lower / two-sided density triple.

---

## Phase 1 — Statement (prose)

`Chebotarev.HasLowerDirichletDensity S δ` is **the relation "the set `S` of prime
ideals of `𝓞 K` has lower Dirichlet density `δ`"**:

> Let `K` be a number field with ring of integers `𝓞 K`, and let `S` be a set of
> ideals of `𝓞 K`. Write `N𝔭 = Ideal.absNorm 𝔭` for the absolute norm. Form the
> partial Dirichlet series over the nonzero prime ideals lying in `S`,
> `P_S(s) = Σ_{𝔭 ∈ S, 𝔭 prime, 𝔭 ≠ 0} N𝔭^{-s}`, and the full one `P(s) = P_{univ}(s)`.
> Then `S` **has lower Dirichlet density** `δ ∈ ℝ` iff the *inferior limit* of the
> ratio `P_S(s) / P(s)` as `s` decreases to `1` from above equals `δ`:
> `δ_inf(S) = liminf_{s → 1⁺} P_S(s)/P(s)`.

This is the standard **lower (analytic) Dirichlet density** of a set of primes —
the `liminf` companion of the two-sided Dirichlet density. Its raison d'être is
exactly that not every set of primes has a well-defined Dirichlet density (a
two-sided limit), but every set has a well-defined lower density (a liminf), so the
liminf/limsup pair is what equidistribution sandwich arguments are phrased in. In
this project it is one leg of the Chebotarev sandwich (Sharifi 7.2.2 Step 2): the
proof bounds `δ_inf ≤ δ_sup` and squeezes them to the target `|C|/|G|`.

**Variables / typeclasses (Lean side):**
- `{K : Type*} [Field K] [NumberField K]` — the number field. `NumberField`
  supplies finiteness of `𝓞 K / 𝔭` (so `absNorm` is meaningful) and the
  convergence of the prime-ideal zeta series for `Re s > 1`.
- `(S : Set (Ideal (𝓞 K)))` — the set of prime ideals tested (primality + nonzero
  cut applied inside `primeIdealZetaSum`).
- `(δ : ℝ)` — the candidate lower-density value.

**Hypotheses (Lean side):** none — it is a definition (a `Prop`), not a theorem.

**Conclusion (math):** `S` has lower Dirichlet density `δ` (a property of `(S, δ)`).

**Conclusion (Lean):** `Prop`, namely
`liminf (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) = δ`.

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

```
Verdict: BIG
Reason: it introduces a NAMED mathematical structure/notion — the LOWER Dirichlet
density of a set of primes — as a new `def`. It is a `## Main definitions` entry of
the file (Density.lean:29) and a structural component of the central Chebotarev
sandwich argument. Named-after-a-mathematician concept (Dirichlet). The
new-named-notion and main-definition BIG triggers both fire.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL recorded for framing.)
```

### One-line check (Phase 2b)

```
Body line count: 3 substantive lines (the `liminf`, the ratio function, the filter
                 `𝓝[>] 1`, set `= δ`) — NOT a one-substantive-line body.
One-liner verdict: MULTI-LINE.
```

A `def` whose body is a `Filter.liminf` of a non-trivial ratio function along a
neighbourhood filter, set equal to `δ`, is multi-line; the one-liner negative-signal
analysis does not apply. (Were it judged a one-liner, exemption #3 "semantic intent /
API name" would still apply — the `HasLowerDirichletDensity.mono` sandwich chain and
the Cyclotomic.lean result conclusion depend on the stable name; see Phase 6.0.)

---

## Phase 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                     | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | lower Dirichlet density liminf set of primes definition number field                       | yes  | **ratio form**: `δ_inf(S) = liminf_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s})/(Σ_𝔭 N𝔭^{-s})`, notated `\underline{δ}_{Dir}(S)` | Wikipedia "Dirichlet density" gives the liminf **ratio** form verbatim; also the equal `liminf … /(-log(s-1))` log form. This is the project's exact form. Explicitly motivates it: "not all sets have a well-defined limit (Dirichlet density) but may have a well-defined liminf". |
| 2  | WebSearch (general / log form)   | "lower Dirichlet density" liminf analytic density prime ideals                              | yes  | log form `liminf_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s})/(-log(s-1))` ≡ ratio | Wikipedia + Encyclopedia of Math; extends to prime ideals of a number field via `N(𝔭)^{-s}`; "regular set" ⟹ density exists, otherwise liminf/limsup. Log ≡ ratio because `Σ_𝔭 N𝔭^{-s} ~ log(1/(s-1))`. |
| 3  | WebSearch (named-after / aliases)| upper lower Dirichlet density limsup liminf Serre Course in Arithmetic                      | yes  | upper = `limsup`, lower = `liminf` of the ratio of Dirichlet series; "if upper and lower coincide, the common value is the Dirichlet density" | Kedlaya ANT ch.4 (kskedlaya.org/ant) + MIT 18.785 LN define **upper/lower Dirichlet density of S in T** via limsup/liminf of the ratio, and the coincidence ⟹ density. Exactly mirrors the project's `HasDirichletDensity.of_upper_eq_lower`. Context attributed to Serre, *A Course in Arithmetic*. |
| 4  | ChatGPT MCP                      | (5-part question on equivalence / generality / liminf-limsup convention)                   | n/a  | — | **MCP treated as down** (per environment note / sibling report Codex-exec failure). Substituted by channels 5–10 per the documented fallback. |
| 5  | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/` and `refs/Chebotarev/`             | n/a  | (no `references/` dir under `.mathlib-quality/`; no `refs/Chebotarev/` store present) | dir absent — recorded n/a. (Module docstring cites `docs/algnum.pdf` = Sharifi §7.1.13; not on disk in this checkout.) |
| 6  | nLab / nCatLab                   | nLab analytic density / Dirichlet density primes                                           | part | "Dirichlet (analytic) density … easier than natural density; `lim (Σ_{p∈S} 1/p^z)/log(1/(z-1))`" | nLab `density` page indexed; analytic-NT concept, not categorical → no dedicated nLab page; upper/lower via liminf/limsup is the standard refinement. Matches #2. |
| 7  | Stacks Project                   | Stacks Dirichlet density / lower density prime ideals                                       | no   | — | **n/a** — analytic number theory, not an algebraic-geometry / commutative-algebra concept; Stacks has no Dirichlet-density entry. |
| 8  | MathOverflow / Math.SE           | (folded into #2/#3 generality queries)                                                      | yes  | confirms lower = liminf of ratio ≡ liminf of log-normalised; lower density exists for all sets | Lower/upper Dirichlet density is the standard tool precisely when the two-sided density may not exist (Benford/leading-digit sets are the textbook example where natural density fails but Dirichlet bounds survive). |
| 9  | Lecture notes (Conrad / Kedlaya / MIT 18.785) | Conrad "Dirichlet density for global fields"; Kedlaya ANT ch.4; MIT 18.785 dirichlet.pdf | yes  | global-field upper/lower def; `Σ_𝔭 N𝔭^{-s} = -log(s-1)+O(1)`; lower = liminf ratio | Kedlaya ch.4 + MIT LN state the **lower/liminf ratio** form explicitly for `S ⊆ T`; number-field/global-field scope; Conrad title "for **global fields**". |
| 10 | recent arXiv (≤5 yr)             | lower Dirichlet density liminf stable sets of primes number field                          | yes  | `\underline{δ}_{Dir}(S) := liminf_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s})/(-log(s-1)) = liminf … /(Σ_𝔭 N𝔭^{-s})` | arXiv 1309.2800 "Stable sets of primes in number fields" uses the **lower Dirichlet density** with the exact ratio≡log liminf definition over prime ideals of a number field; also 2009.10431 (Neukirch–Uchida w/ restricted ramification). Confirms the form is current and standard for prime-ideal sets, but neither is mathlib. |

### Literature summary (Phase 3)

```
Concept identified as: LOWER Dirichlet density (a.k.a. lower analytic density),
                       notated δ_inf(S) or \underline{δ}_{Dir}(S), of a set of prime
                       ideals of a number field / set of places of a global field.
                       It is the liminf member of the standard upper/lower
                       (limsup/liminf) Dirichlet-density pair.
Sources agree on the standard form: YES — two equivalent normalisations of the liminf:
  (A) ratio:   liminf_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})     ← THE PROJECT'S FORM
  (B) log:     liminf_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s}) / (-log(s-1))
  Equivalence: because Σ_𝔭 N𝔭^{-s} ~ log(1/(s-1)) = -log(s-1)+O(1) as s→1+
  (Wikipedia, Encyclopedia of Math, Kedlaya ch.4, MIT 18.785, arXiv 1309.2800 all
  state this; Wikipedia presents the RATIO liminf as the primary lower-density form).
Most general standard form: a set of (finite) places / nonzero primes of a GLOBAL
  field K, lower density = liminf of ratio (A) (equivalently (B)).
Generality dimensions where the literature varies:
  - base object: rational primes ⊂ prime ideals of a number field ⊂ places of a
    global field (number field OR function field F_q(t)). Most general = global field.
  - normalisation: ratio (A) vs log (B) — equivalent for value; both standard; (A)
    is the more common primary form for the liminf.
Disagreement with the literature: NONE on the mathematics. The project's def is the
  liminf in normalisation (A), the primary textbook lower-density form, at the
  number-field generality.
LABELLING NOTE (project-internal, correctness-relevant but not a literature
  disagreement): the file's docstring (Density.lean:69–92) flags that Sharifi's
  *Algebraic Number Theory* §7.1.13 INVERTS the "upper/lower" labels — Sharifi calls
  the liminf "upper" (δ_inf). The project deliberately follows the STANDARD convention
  (lower = liminf), which channels 1, 3, 9 confirm is the mathematically standard
  one. So `HasLowerDirichletDensity = liminf` is correctly named per the literature;
  only Sharifi's notes are non-standard, and the file documents this explicitly.
```

The standard literature thus matches the Lean def precisely: lower Dirichlet
density **= liminf of the ratio of partial Dirichlet series**, with the
upper/lower pair existing exactly so that the sandwich `δ_inf ≤ δ_sup` (and their
coincidence ⟹ density) can be stated — which is the structural role the def plays
in this project's `HasDirichletDensity.of_upper_eq_lower` (Density.lean:228) and
`HasLowerDirichletDensity.mono` (Density.lean:256).

---

## Phase 4 — Generality analysis

### Generality analysis — `Chebotarev.HasLowerDirichletDensity` (Phase 4a)

Literature-standard form (from Phase 3): the **liminf of the ratio**
`liminf_{s→1⁺} P_S(s)/P(s)`, for a set of nonzero primes / finite places of a
**global field**.

| # | Parameter / hypothesis     | Current Lean form                    | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|--------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K]`          | K a number field                     | K a global field (number **or** function field) | **partially — NOT mechanically** | The function-field case uses a *different* size normalisation: places weighted by `q^{-s·deg}`, not `Ideal.absNorm^{-s}` over `𝓞 K`. Mathlib has **no `GlobalField` typeclass** (only a separate `FunctionField` abbrev) and `Ideal.absNorm` is the number-field (finite-residue-cardinality) norm. A genuine global-field def needs infrastructure mathlib lacks; it is NOT a typeclass-weakening of this def, it is a separate larger development. |
| 2 | normalisation = ratio (A)  | `liminf (P_S(s)/P_{univ}(s))`        | liminf of ratio (A) **or** log (B) `/(-log(s-1))` | equivalent, not "weaker" | (A) and (B) define the same lower density; (A) is the primary textbook form. No generality lost by (A); see Phase 4c for the idiom question. |
| 3 | `S : Set (Ideal (𝓞 K))`    | set of ideals (primality cut inside) | set of nonzero primes                    | NO (already maximally permissive) | Taking `S : Set (Ideal …)` and filtering `𝔭.IsPrime ∧ 𝔭 ≠ ⊥` inside `primeIdealZetaSum` is *more* flexible than requiring `S ⊆ {primes}`; lets callers feed arbitrary ideal sets. Good as is. |
| 4 | target `δ : ℝ` via `liminf … = δ` | liminf equals a given real `δ`       | liminf is the lower density value `δ_inf` | NO | `Filter.liminf` into `EReal`/`ℝ` is always defined, so the `= δ` formulation is the right "has lower density δ" relation. Pinning `δ : ℝ` (not `EReal`) matches the bounded setting: the ratio is in `[0,1]` for `s>1` (`eventually_primeIdealZetaSum_ratio_le_one`, Density.lean), so the liminf is a genuine real. |

### Generality verdict (Phase 4b)

```
The current form is: MAXIMALLY GENERAL (within the number-field setting, which is
                     the right and standard setting for an `Ideal.absNorm`-based
                     lower density).
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
| 2  | sequences/metric where filters/topology generalise? | **already done** | the def **already** uses `Filter.liminf … (𝓝[>] 1)` — the modern filter idiom, not an `ε`-`δ` or sequential `s_n ↓ 1` formulation | composes with all of mathlib's `liminf` / `nhdsWithin` order API (`liminf_le_liminf`, `isBoundedUnder`/`isCoboundedUnder`, `le_liminf_of_le`) — which Density.lean's `mono`/`of_upper_eq_lower` proofs already exploit |
| 3  | construct an object where a universal-property class would characterise it? | no | a lower density is a numeric liminf, no universal property | — |
| 4  | set-with-closure-predicate → bundled substructure? | no | `S` is genuinely an arbitrary set of ideals; no substructure | — |
| 5  | vector-space/metric/field-specific → weaken typeclasses? | no | `[NumberField K]` is load-bearing (finite residue fields, zeta convergence) | — |
| 6  | 1-categorical → higher-categorical? | no | not categorical | — |
| 7  | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | no | the index `s : ℝ` is the real Dirichlet-series variable; intrinsic to the analytic notion | — |

```
### Modern-idiom verdict (Phase 4c)
Modern idiom available: NO new idiom to apply — the def is ALREADY in the
contemporary mathlib idiom (filter-based `Filter.liminf … (𝓝[>] 1) = δ`, a
Prop-valued relation, rather than a sequential `s_n ↓ 1` liminf or a junk-valued
partial real function). `Filter.liminf` is total (always defined), so the `= δ`
relation is exactly the right "has lower density δ" packaging — value-uniqueness is
automatic (a liminf is unique), no `Classical.choice` needed.
Reason this is not a (further) modernisation move: the only two anchors the
literature offers — the log-normalisation (B) and the global-field generalisation —
are respectively an equivalent restatement (no organisational gain; (A) is primary)
and a genuinely larger development needing absent infrastructure, not a reformulation.
```

The `Filter.liminf … = δ` packaging is the idiomatic mathlib choice over a
junk-valued `lowerDirichletDensity S : ℝ`: `liminf` is always defined, so no side
existence hypothesis is needed, and it sits in deliberate parallel with the
companion `HasUpperDirichletDensity` (`limsup`) and `HasDirichletDensity`
(`Tendsto`). The triple mirrors mathlib's own `limsup`/`liminf`/`Tendsto` order-API
layering.

---

## Phase 4.5 — Diamond / defeq risk (kind = `def`)

`HasLowerDirichletDensity` is a `Prop`-valued `def` (a named proposition asserting a
`liminf` equals `δ`). It defines **no** new data, instance, coercion, or algebraic
operation — it is a named predicate. The diamond/defeq risk surface is near-empty,
but the six rows are filled for completeness.

### Diamond / defeq risk — `Chebotarev.HasLowerDirichletDensity` (Phase 4.5a)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | Not an `instance`; introduces no typeclass and no instance-search path. |
| 2 | Reducibility leak            | none    | Not `@[reducible]`. Callers `rw [HasLowerDirichletDensity]` to unfold explicitly (Density.lean:259, and in `hasLower`/`of_upper_eq_lower` via the `liminf_eq` projection) — the seal is wanted, not a leak. |
| 3 | Non-canonical unfolding      | low     | It is definitionally a `liminf … = δ`; `unfold`/`rw [HasLowerDirichletDensity]` exposes the equation. No surprising `rfl`/`simp` behaviour beyond that one explicit unfold. |
| 4 | Instance priority collision  | none    | Not an `instance`; no priorities. |
| 5 | Universe-polymorphism issues | none    | `K : Type*` with `[Field K] [NumberField K]`; the proposition lands in `Prop`; no universe annotation forced. |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort`; the only coercion in the body is the standard `ℕ → ℝ` on `absNorm`, already canonical. (`Filter.liminf` here is the `ℝ`-valued / conditionally-complete-lattice one, the same instance the companion `limsup` def uses.) |

### Risk verdict (Phase 4.5)

```
Overall risk: NONE
Top risks: none
Recommended mitigations: none required.
```

---

## Phase 5 — Mathlib search

Five-method search. Lean MCP tools (Loogle / LeanSearch / Lean-Finder) are **not
exposed** in this environment and the build is stale; methods [A][B][C] are therefore
run as `grep` over the vendored mathlib source (commit `d90090f647`, authoritative
for presence), and [E] as a name grep. Both the **user's form** (number-field
prime-ideal liminf ratio) and the **literature-standard general form** (any
lower/analytic-density-of-primes notion) were searched.

```
### Mathlib search-status: `Chebotarev.HasLowerDirichletDensity`

[A] Lean-Finder       (unavailable)              n/a: MCP not exposed in this env
[B] Loogle            (unavailable)              n/a: MCP not exposed; substituted by [D] grep over type-shape
[C] LeanSearch        (unavailable)              n/a: MCP not exposed; substituted by [D] grep over concept terms
[D] Grep mathlib src  `DirichletDensity`, `dirichlet.{0,3}density`, `lowerDensity`,
                      `upperDensity`, `analyticDensity`, `HasLowerD`, `HasUpperD`,
                      and `liminf|limsup` ∩ `densit|prime` in NumberTheory/
                        →  NO hits for ANY density-of-primes notion (lower or
                           otherwise). The `liminf`/`limsup` ∩ density/prime grep
                           over Mathlib/NumberTheory/ returns EMPTY.
[E] Name pattern      `HasLowerDirichletDensity`, `lowerDirichletDensity`,
                      `dirichletDensity`  →  no hits.

Searched for both:
  - user's current form (number-field prime-ideal liminf ratio): NOT in mathlib.
  - literature-standard general form (lower/analytic Dirichlet density of primes,
    global-field version): NOT in mathlib.

Adjacent infrastructure that DOES exist (relevant for Phase 6):
  - `NumberField.dedekindZeta`, `NumberField.dedekindZeta_residue`,
    `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (the Dirichlet class
    number formula)  — Mathlib/NumberTheory/NumberField/DedekindZeta.lean. This is
    the ζ_K residue at s=1, the analytic ingredient NEAR the density (it powers the
    eventual `P_univ(s) ~ log(1/(s-1))` denominator asymptotic), but is NOT a
    density notion and NOT the per-prime partial-sum liminf-ratio.
  - `Filter.liminf` / `Filter.limsup` and their full order API (the building block
    the def is BUILT FROM) — Mathlib/Order/LiminfLimsup.lean — present and used by
    the def, but generic, not a density.
  - mathlib has NO `GlobalField` typeclass and NO Chebotarev / Frobenius-density
    theorem.

Concluded: NOT in mathlib (all available methods exhausted, plus the
literature-standard general form). Mathlib has neither this def nor any
lower-/analytic-density-of-primes notion in any form.
```

---

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `Chebotarev.HasLowerDirichletDensity` (Phase 6.0)

```
Internal use count: 4  (within the Chebotarev project, NOT counting the declaring
                    file Density.lean): 3 term-level uses in Abelian.lean + 1 result
                    conclusion in Cyclotomic.lean.
External-to-file callers: 2 distinct files (Abelian.lean, Cyclotomic.lean).
Plus 4 in-file uses in Density.lean (the def's own API layer): the def itself (89),
    `of_upper_eq_lower` hypothesis (229), `hasLower` conclusion (242),
    `mono` statement + unfold (256–259).
```

| Caller file:line                    | Usage pattern (one-line excerpt)                                                |
|-------------------------------------|---------------------------------------------------------------------------------|
| CebotarevDensity/Abelian.lean:877   | `have hUlow : HasLowerDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := hUdens.hasLower` |
| CebotarevDensity/Abelian.lean:878   | `have hSσlow : HasLowerDirichletDensity Sσ …` (the conjugacy-class fibre's lower density) |
| CebotarevDensity/Abelian.lean:882   | `have hmono := HasLowerDirichletDensity.mono hUsub hUlow hSσlow` (the sandwich `δ_inf ≤ δ_inf` step) |
| CebotarevDensity/Cyclotomic.lean:997| `… HasLowerDirichletDensity …` (conclusion of a cyclotomic lower-density bound; per the line-993 docstring, fed into the `HasLowerDirichletDensity.mono` chain) |

```
Inline-derivation grep (was the liminf-ratio re-spelled elsewhere without using
`HasLowerDirichletDensity`?):  (none) — every site goes through the named def or its
`.mono`/`.hasLower` API; the `liminf (… P_S/P_univ …) (𝓝[>] 1) = δ` shape never
appears open-coded in a consumer.
```

**Signal (per the call-sites table):** K = 4 internal uses across 2 files (plus the
def's own 4-lemma API layer in Density.lean), **no** inline re-derivation anywhere →
this is a real, load-bearing API: it is one of the two legs of the Chebotarev
sandwich (`HasUpperDirichletDensity` is the other), and the `mono` chain that
squeezes the density is phrased entirely through the named def. Consumers depend on
the stable name. **YES-\*** lean.

### Composition check (Phase 6a)

```
Can `Chebotarev.HasLowerDirichletDensity` be derived from mathlib in ≤3 chained calls?

Attempt 1: `liminf (P_S / P_univ) (𝓝[>] 1) = δ` — this is what the def IS. The body
  is built from `Filter.liminf`, `nhdsWithin`, `tsum`, `Ideal.absNorm`, `Real.rpow` —
  all mathlib primitives. But assembling them is *spelling a definition*, not
  *deriving a statement*: there is no mathlib lemma whose conclusion is this liminf
  equation, because the very notion "lower Dirichlet density" is absent from mathlib.
  A `def` cannot be "composed away" the way a lemma can — the question for a def is
  whether mathlib already names this concept (Phase 5: no) and whether it is the
  right concept (Phases 3–4: yes, it is the standard lower-density notion).
  Result: not applicable in the lemma sense — this is a definitional anchor, not a
  derivable proposition.

Conclusion: NOT-COMPOSABLE (as a "use mathlib at the call site instead" move).
  Mathlib has the *raw* `Filter.liminf`/`tsum`/`absNorm` constructors, but no named
  lower-Dirichlet-density concept; inlining the bare `liminf … = δ` at the call sites
  (instead of the named def, and instead of going through `.mono`/`.hasLower`) would
  DESTROY the API and the sandwich abstraction, not compose it. The named def is
  exactly what the consumers and the `mono`/`of_upper_eq_lower` lemmas need. The
  `dedekindZeta_residue` infra is *adjacent* (it powers the eventual denominator
  asymptotic) but is not this definition and does not compose to it in ≤3 calls.
```

---

## Phase 7 — Verdict

```
## Verdict: `Chebotarev.HasLowerDirichletDensity`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): the LOWER (analytic) Dirichlet density of a set of
  primes is a canonical, named concept (Dirichlet), notated δ_inf / \underline{δ}_{Dir};
  the liminf of the RATIO `P_S/P` is the PRIMARY textbook form (Wikipedia) and is
  EXACTLY the project's form, with the log-normalisation an equivalent. Kedlaya ANT
  ch.4 + MIT 18.785 + arXiv 1309.2800 give the lower/liminf ratio form explicitly for
  prime-ideal sets of a number field; ≥9 channels concur, no mathematical disagreement.
  The upper/lower (limsup/liminf) pair is standard precisely so the sandwich can be
  stated — which is the role this def plays here.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the number-field setting
  (the correct setting for an `Ideal.absNorm`-based density). 0 mechanical weakenings.
  The lone "more general" anchor (global fields) is a separate larger development
  needing infrastructure mathlib lacks, NOT a restatement. Phase 4c: the def is
  ALREADY in the modern filter-`liminf`/`Prop`-relation idiom.
- Mathlib search (Phase 5): NOT in mathlib — no lower-/analytic-density-of-primes
  notion in ANY form; no DirichletDensity / lowerDensity name; no liminf-density in
  NumberTheory/; no Chebotarev/Frobenius density; no `GlobalField` typeclass.
- Composition check (Phase 6): NOT-COMPOSABLE — a definitional anchor used by the
  Chebotarev sandwich (Abelian.lean `mono` chain, Cyclotomic.lean conclusion) with
  zero inline re-derivation; bare `liminf` constructors exist but do not constitute a
  named concept, and inlining would destroy the sandwich API.
- Diamond/defeq risk (Phase 4.5): NONE (Prop-valued predicate, no instance/coercion/data).

**Rationale:**

Lower Dirichlet density is a standard, named refinement of one of analytic number
theory's foundational size-measures: the liminf member of the upper/lower
(limsup/liminf) Dirichlet-density pair, which exists precisely because not every set
of primes has a two-sided Dirichlet density but every set has a well-defined lower
density. Wikipedia states the liminf-of-the-ratio form `\underline{δ}_{Dir}(S) =
liminf_{s→1+} (Σ_{𝔭∈S} N𝔭^{-s})/(Σ_𝔭 N𝔭^{-s})` as the primary lower-density
definition, identical to the Lean def; Kedlaya ANT ch.4, MIT 18.785, and the
"stable sets of primes" literature (arXiv 1309.2800) all use the same form for prime
ideals of a number field. Mathlib today has the Dedekind zeta function and its
residue at `s=1` (`NumberField.dedekindZeta_residue`,
`tendsto_sub_one_mul_dedekindZeta_nhdsGT`) but **no notion of the density of a set of
primes at all** — the exhaustive grep over commit `d90090f647` finds zero hits under
the number-field form, any general form, or any liminf/limsup-density spelling. That
is the concrete, nameable gap: a library that has the class number formula but cannot
*state* "this set of primes has lower density δ" is missing the vocabulary every
equidistribution sandwich (Chebotarev, Dirichlet-AP, splitting density) is phrased
in. The two leg defs `HasUpperDirichletDensity` (limsup) and
`HasLowerDirichletDensity` (liminf) are exactly that vocabulary, in the primary ratio
normalisation, packaged as `Prop`-valued relations in deliberate parallel with
mathlib's own `limsup`/`liminf` and `HasSum`/`HasDerivAt` style — the idiomatic choice
that makes value-uniqueness automatic (`liminf` is total, no `Classical.choice`) and
that the file uses to power `HasDirichletDensity.of_upper_eq_lower` and
`HasLowerDirichletDensity.mono`.

On generality: the number-field restriction is correct, not a deficiency. The
function-field ("global field") case is genuinely different at the level of the size
weight (degree-based `q^{-s·deg}` rather than `Ideal.absNorm^{-s}`), mathlib has no
`GlobalField` typeclass to hang a unified def on, and `Ideal.absNorm` is intrinsically
the number-field norm. So there is no mechanical weakening to perform first — this is
the maximally-general form expressible with present mathlib infrastructure, and the
verdict is YES-add-as-is rather than YES-but-generalise-first. This decl is the exact
liminf sibling of `HasDirichletDensity` (assessed YES-add-as-is in this directory) and
should ship in the same PR.

**WHY add it (refactor-actionable):**
- New content mathlib is missing: the LOWER (analytic) **Dirichlet density of a set of
  prime ideals** of a number field — there is no such def, nor any lower/upper
  density-of-primes notion, in mathlib (Phase 5 exhaustive grep: zero hits, all
  forms). The specific gap: mathlib has `NumberField.dedekindZeta` + its `s=1` residue
  but no way to *state* a lower-density-of-primes bound; every equidistribution
  sandwich argument (Chebotarev's `δ_inf ≤ δ_sup` squeeze, Dirichlet-AP lower bounds,
  splitting-density bounds) needs the liminf vocabulary and currently cannot be stated
  in mathlib at all.
- How it composes with mathlib: as a `Filter.liminf … (𝓝[>] 1) = δ` predicate it
  immediately inherits the full `liminf`/`nhdsWithin` order calculus — `liminf_le_liminf`,
  `isBoundedUnder`/`isCoboundedUnder_ge`, `le_liminf_of_le`, and the
  `tendsto_of_liminf_eq_limsup` bridge to the two-sided `HasDirichletDensity` (all of
  which the Density.lean `mono`/`of_upper_eq_lower` proofs already use). The companion
  `limsup` (upper) and `Tendsto` (two-sided) defs slot into the same order API, and
  the `dedekindZeta_residue` API supplies the denominator asymptotic for proving
  concrete lower densities.

Proposed mathlib location:   Mathlib/NumberTheory/NumberField/DirichletDensity.lean
                             (sits naturally beside DedekindZeta.lean, which supplies
                             the s=1 analytic input; namespace `NumberField` rather
                             than the project's `Chebotarev`).
Proposed PR title:           "feat(NumberTheory): Dirichlet density of a set of prime ideals"
PR grouping:                 ship `HasLowerDirichletDensity` TOGETHER with its siblings
                             `HasDirichletDensity`, `HasUpperDirichletDensity`,
                             `primeIdealZetaSum`, and the basic API lemmas from
                             Density.lean (empty / finite / monotone / union / disjoint,
                             `of_upper_eq_lower`, `hasUpper`/`hasLower`,
                             `HasLowerDirichletDensity.mono`,
                             `infinite_of_hasDirichletDensity_pos`) as ONE coherent
                             "Dirichlet density" PR — the lower-density def is not
                             useful to mathlib in isolation from the upper/two-sided
                             defs and the sandwich lemma. The upper/lower convention
                             note (vs Sharifi's inverted labels, Density.lean:69–92)
                             MUST be preserved in the docstring — it is correctness-
                             relevant for anyone transcribing Sharifi.
Pre-PR checklist before opening:
  - [ ] /generalise Chebotarev.HasLowerDirichletDensity — confirm no easy further
        weakening (expected: none beyond the global-field non-starter; sanity-check
        whether `[NumberField K]` could be spelt via a weaker mixin once the
        zeta-convergence lemmas it needs are isolated).
  - [ ] /cleanup CebotarevDensity/Density.lean — full audit + diff gates on the whole
        density-API block (all three defs + their lemmas) to mathlib style.
  - [ ] Decide naming: `NumberField.HasLowerDirichletDensity` vs a `setOf`-based name;
        keep the upper/lower naming consistent across the triple; confirm
        `primeIdealZetaSum` naming against mathlib's `LSeries` conventions.
  - [ ] Pick a reviewer from Mathlib/NumberTheory/NumberField/ recent commits
        (DedekindZeta / L-series area).
```

### Phase 7 gate self-check

- YES-add-as-is requires: Phase 3 lit table ≥3 channels ✓ (10 rows); Phase 4
  generality = MAXIMALLY GENERAL ✓; Phase 4.5 risk NONE ✓; Phase 5 no hit (both
  forms) ✓; Phase 6 NOT-COMPOSABLE ✓; not a one-liner (MULTI-LINE) ✓; bucket-specific
  WHY names a concrete gap (mathlib has ζ_K residue / class number formula but no
  lower-density-of-primes notion) ✓; refactor-actionable PR plan + call-site table
  present ✓.
- Phase 4b was MAXIMALLY GENERAL (not STRICTLY NARROWER) → YES-add-as-is permitted,
  YES-but-generalise-first not forced. ✓
- Phase 4c found no *new* modern idiom to apply (the def already is the modern
  filter-`liminf` idiom) → not pushed to YES-but-generalise-first MODERN-IDIOM. ✓
- Cost was NOT cited as a downgrade reason. The global-field non-generalisation is on
  infrastructure-absence + different-normalisation grounds (a genuine mathematical
  difference), not "too expensive". ✓
- Consistent with the sibling `HasDirichletDensity` verdict (YES-add-as-is) and the
  `HasUpperDirichletDensity` limsup leg — the triple ships as one PR. ✓

---

## Phase 8 — Next step

Run, in order, before any mathlib PR:
1. `/generalise Chebotarev.HasLowerDirichletDensity` — confirm no further weakening
   (expected: none; the global-field form is a separate development, not a weakening).
2. `/cleanup CebotarevDensity/Density.lean` over the whole Dirichlet-density API block
   (the upper / lower / two-sided defs and their lemmas together).
3. Open one grouped `feat(NumberTheory)` PR adding `primeIdealZetaSum`,
   `HasDirichletDensity`, `HasUpperDirichletDensity`, `HasLowerDirichletDensity` and
   their basic lemmas (incl. `of_upper_eq_lower`, `hasUpper`/`hasLower`,
   `HasLowerDirichletDensity.mono`) to
   `Mathlib/NumberTheory/NumberField/DirichletDensity.lean` (namespace `NumberField`),
   preserving the upper/lower-convention docstring note.
```
```
