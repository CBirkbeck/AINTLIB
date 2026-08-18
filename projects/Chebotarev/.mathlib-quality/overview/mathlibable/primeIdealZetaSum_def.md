# /mathlibable report — `Chebotarev.primeIdealZetaSum_def`

> Step-9 mathlibable assessment, AINTLIB `/overview`. Single declaration.
> Target: `Chebotarev.primeIdealZetaSum_def`
> Source: `projects/Chebotarev/CebotarevDensity/Density.lean:55`

---

## Baseline (Phase 0)

- lake build:               ⚠ not re-run (local build stale per task brief; reasoned from source + mathlib tree on pin `v4.31.0-rc2`).
- decl `Chebotarev.primeIdealZetaSum_def`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Density.lean:55`.
- kind:                      `theorem` (equation / glue lemma).
- has sorry:                 no — body is literally `:= rfl`.
- module docstring summary:  "Dirichlet density of a set of prime ideals" — partial Dirichlet series, `HasDirichletDensity`, upper/lower variants for the Chebotarev sandwich (Sharifi §7.1).

**Parent declaration.** `primeIdealZetaSum_def` is the equation lemma of the
`def primeIdealZetaSum` two lines above it (`Density.lean:50`):

```lean
def primeIdealZetaSum (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- Equation lemma unfolding `primeIdealZetaSum` to its defining `tsum`. -/
theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl
```

So this is a **glue lemma** in the precise sense of the mathlibable verdict
reference (body = `rfl`). Per the verdict-inheritance rule, its mathlibability
is determined by — and inherits from — the parent `def primeIdealZetaSum`. The
literature / mathlib / generality analysis below is therefore conducted on the
**parent def**, and the verdict propagated to the equation lemma.

---

## Statement (Phase 1)

`primeIdealZetaSum_def` asserts that the bookkeeping function `primeIdealZetaSum S s`
is *definitionally equal* to the `tsum` (unconditional sum) that defines it:

> For a number field `K`, a set `S` of ideals of `𝓞 K`, and a real `s`,
> `primeIdealZetaSum S s = Σ'_{𝔭} N(𝔭)^{-s}`, where the sum runs over the
> subtype of ideals `𝔭` that lie in `S`, are prime, and are nonzero, and
> `N(𝔭) = Ideal.absNorm 𝔭` is the absolute norm.

Mathematically the *content* is the parent object: the **partial Dirichlet
series** (partial Dedekind / prime zeta sum) `P_S(s) = Σ_{𝔭 ∈ S} N(𝔭)^{-s}`
restricted to the nonzero primes of `S`, with a **real** exponent. This is the
numerator in the Dirichlet-density ratio `δ(S) = lim_{s↓1} P_S(s) / P_univ(s)`
(Sharifi 7.1.13; the denominator `~ log(1/(s−1))`).

Variables / typeclasses (Lean side):
- `{K : Type*} [Field K] [NumberField K]` — the number field.
- `(S : Set (Ideal (𝓞 K)))` — the set of (ideals containing the) primes summed over.
- `(s : ℝ)` — the real exponent.

Hypotheses: none (it is an unconditional `rfl`; convergence is not asserted here —
summability lives in the separate `summable_prime_absNorm_rpow`).

Conclusion (math): the function equals its defining series — a pure unfolding.
Conclusion (Lean): `primeIdealZetaSum S s = ∑' …`.

---

## Size classification (Phase 2a)

Verdict: **SMALL** (the equation lemma itself). The *parent* `def primeIdealZetaSum`
is borderline-BIG (it introduces a named analytic-number-theory object), but the
equation lemma is a one-line `rfl` helper.

Reason: `primeIdealZetaSum_def` is a definitional-unfolding helper; not a main
result, not named after a person, introduces no new structure. (Literature width
was run EXHAUSTIVE regardless, aimed at the parent object.)

---

## One-line check (Phase 2b)

Body line count: 1 substantive line (`:= rfl`).
One-liner verdict: **n/a for the def-exemption table** — kind is `theorem`, not `def`.
But it *is* a one-line `rfl` glue lemma, which is itself a strong signal that it
is not an independent contribution: it exists only to control the unfolding of
`primeIdealZetaSum` inside `rw` chains.

Note (parent def, for completeness): `primeIdealZetaSum` is a **MULTI-LINE-ish**
`def` (a single `tsum` over a 3-condition subtype). It carries a docstring and a
stable name that 4 other files `rw` against, so it has real API-surface value
*within the project* — but that does not by itself make it mathlib-idiomatic
(see Phase 4c).

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                              | Query                                                                                                  | Hit? | Standard form found                                              | Notes |
|----|--------------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)            | "Dirichlet density set of prime ideals number field partial Dirichlet series sum N(p)^{-s}"           | yes  | `Σ_{𝔭∈A} N(𝔭)^{-s}` as the *numerator* of the density ratio       | Encyclopedia of Math; Conrad (Stanford 676); Snowden (Michigan 776 "L-functions and densities"); Wikipedia |
|  2 | WebSearch (general form)             | "Dirichlet density prime ideals definition limit s to 1 Dedekind zeta log(1/(s-1))"                   | yes  | `δ(A)=lim_{s↓1} (Σ_{𝔭∈A}N𝔭^{-s})/log(1/(s−1))`; also the `1−s` regular-part variant | confirms the sum is the *building block*, density is the ratio; ties to Dedekind ζ pole of order 1 |
|  3 | WebSearch (named-after / aliases)    | (covered by #1/#2) "analytic density", "prime zeta sum", "partial zeta function" of a set of primes    | partial | "analytic density" = synonym for Dirichlet density; the partial sum has **no standard proper name** | the sum `Σ_{𝔭∈A}N𝔭^{-s}` is consistently written inline, unnamed |
|  4 | ChatGPT MCP                          | "Is `P_S(s)=Σ_{𝔭∈S}N𝔭^{-s}` a standard named object? How do Neukirch/Serre/Lang/Marcus/Stevenhagen-Lenstra treat it? real vs complex s?" | n/a  | —                                                                | MCP **down** in this env (Codex exec failed on both `gpt-5.4` and `gpt-5.4-mini`); fell back to WebSearch + primary-source notes per task brief |
|  5 | Local references                     | grep `.mathlib-quality/references/` for "density"                                                      | n/a  | (no references dir)                                              | `projects/Chebotarev/.mathlib-quality/references/` absent — recorded n/a. In-source cites: Sharifi §7.1.12–7.1.13 (`docs/algnum.pdf`), Stevenhagen–Lenstra (`docs/cheb.pdf`) |
|  6 | nLab                                 | "Dirichlet density"                                                                                    | no   | nLab has no "Dirichlet density" page (404)                       | concept lives in classical ANT, not the nLab abstract-nonsense corpus |
|  7 | nCatLab (if categorical)             | —                                                                                                      | n/a  | not a categorical concept                                       | a real-analytic limit of a Dirichlet series; no categorical content |
|  8 | Stacks Project (if alg geom)         | —                                                                                                      | n/a  | not an algebraic-geometry concept                              | Stacks covers schemes/comm-alg, not analytic densities of primes |
|  9 | MathOverflow / Math.StackExchange    | "Dirichlet density prime ideals partial sum named" (via #1/#3 result set)                              | partial | community consistently treats `Σ N𝔭^{-s}` as auxiliary; no canonical name | reinforces "auxiliary expression, not a named object" |
| 10 | recent arXiv (last 5 years)          | "Chebotarev density" + "Dirichlet density positive" (arXiv 2210.13412 supplement; 2603.27472)         | yes (concept) | uses `Σ_{𝔭}N𝔭^{-s}` inline; density via the ratio/regular-part | modern papers still inline the sum; no separate `def` for the partial sum |

Protocol-pass check:
- WebSearch ran **≥3 distinct queries** at different generality (specific numerator form #1, full density definition #2, aliases / proper-name search #3). ✓
- ChatGPT MCP: attempted, **unavailable** (down per the environment note) — recorded n/a with reason and substituted primary-source lecture notes (Conrad, Snowden) that explicitly discuss the standard form, generality, and historical framing. ✓ (fallback honoured)
- Local references checked (absent → n/a with reason). ✓
- nLab checked (404, no page). ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: the **partial Dirichlet series / partial (Dedekind) zeta
sum over a set of prime ideals**, `P_S(s) = Σ_{𝔭 ∈ S} N(𝔭)^{-s}` — the *numerator*
of the **Dirichlet (analytic) density** of `S`.

Sources agree on the standard form: **yes**, with one important caveat — every
source treats `Σ_{𝔭 ∈ S} N(𝔭)^{-s}` as an **auxiliary, unnamed expression that
appears only inside the density definition**. It is *not* a standalone named
object with its own notation. The *named* objects in the literature are (a) the
**Dirichlet density** `δ(S)` itself, and (b) the **Dedekind zeta function**
`ζ_K(s) = Σ_I N(I)^{-s}` over *all* ideals (the `S = univ` prime-restricted
cousin is `log ζ_K(s) + O(1)`).

Most general standard form: the partial sum is stated over an arbitrary set of
primes of a **global field** (number field *or* function field), and the
classical analytic input (`ζ_K` has a simple pole at `s=1`) is phrased with a
**complex** variable `s`, the density being the `s ↓ 1` real limit of the ratio.

Generality dimensions where the literature varies:
  - **exponent `s`**: real (for the density limit itself) vs **complex** (for the
    analytic backbone — Dedekind ζ / Hecke L-series; this is the modern default,
    and the one mathlib already uses). Range: ℝ (this project) … ℂ (mathlib `LSeries`).
  - **base field**: number field (this project) … global field (number + function
    fields).
  - **named vs inlined**: uniformly **inlined** into the density definition; no
    textbook (Neukirch, Serre *Course in Arithmetic* §VI, Lang *ANT*, Marcus,
    Stevenhagen–Lenstra) gives the partial prime sum its own `def`.

Disagreement with the literature: the project uses a **real** exponent and a
**bespoke real-valued `def`** for the partial sum, where the modern/standard
analytic treatment is **complex** and routes everything through the (already-
in-mathlib) Dedekind-ζ / `LSeries` machinery. Not "wrong" — but a deliberately
elementary, project-local reformulation.

---

## Generality analysis — `primeIdealZetaSum` (parent) / `primeIdealZetaSum_def`

Literature-standard form (from Phase 3): the analytic object underlying the
density is the **complex** Dedekind ζ / Hecke `L`-series; the prime-restricted
*partial sum* is an inline auxiliary `Σ_{𝔭∈S} N𝔭^{-s}`.

| # | Parameter / hypothesis            | Current Lean form                       | Literature-standard form                          | Weaker/more-general form exists? | Reason |
|---|-----------------------------------|-----------------------------------------|---------------------------------------------------|----------------------------------|--------|
| 1 | `(s : ℝ)`                         | real exponent                           | complex exponent (analytic continuation; ζ_K, LSeries) | yes (ℝ → ℂ)                | mathlib's whole zeta/L-series API (`LSeries`, `dedekindZeta`) is **complex**; the real `s` is a specialisation chosen for the elementary density limit |
| 2 | `[Field K] [NumberField K]`       | number field                            | global field (number or function field)           | yes (number field → global field) | density / Chebotarev hold over global fields; but mathlib's `Ideal.absNorm` + Dedekind-ζ scaffolding is number-field-specific today, so this generalisation is gated by mathlib, not cheap |
| 3 | `(S : Set (Ideal (𝓞 K)))` indexing the subtype `{𝔭 ∈ S ∧ IsPrime ∧ ≠⊥}` | set + 3-predicate subtype | `Set.indicator` of `S` on the prime-norm coefficients of an `LSeries` | yes (modern idiom) | mathlib expresses "restrict a Dirichlet series to a subset" via indicator coefficients of `LSeries`, not a hand-rolled subtype `tsum` |
| 4 | value type `ℝ`, via `tsum`        | real `tsum` (unconditional)             | complex `LSeries` (with explicit summability region) | yes                          | mathlib already has the complex partial-sum/`LSeries` abstraction; a real `tsum` over a subtype is a re-implementation |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER / NON-IDIOMATIC THAN STANDARD** (real,
number-field-specific, bespoke-subtype) relative to the modern complex-`LSeries`
analytic standard — though it is a *deliberate* narrowing for an elementary
real-variable proof of Chebotarev density.

Number of weakening / re-idiomatisation opportunities found: 4 (real→complex,
number-field→global-field, subtype→indicator-`LSeries`, real-`tsum`→`LSeries`).

Proposed restatement: **does not exist as a simple mechanical weakening.** Moving
to the complex/`LSeries` form is a *reformulation*, not a generalisation that
preserves the proof — the entire downstream Chebotarev development is built on the
real `tsum` and its real-analysis lemmas (`tsum_nonneg`, `tsum`-monotonicity,
`liminf`/`limsup` of a real ratio). Restating against complex `LSeries` would
require re-deriving the density theory in mathlib's complex analytic-number-theory
idiom.

Cost of re-idiomatisation: **EXPENSIVE** — needs new ideas / a parallel
development, not a signature tweak. (Per the skill: EXPENSIVE is not a downgrade
in principle, but here it interacts with a genuine design question — see Phase 7.)

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                                  | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let `S` be a set of primes" preamble → typeclass/instance?                                              | no       | `S` is genuinely a varying set argument (the density is a function of `S`); not a class | — |
|  2 | sequences/metric → filters/topological?                                                                  | partial  | already filter-based downstream (`𝓝[>] 1`, `limsup`/`liminf`); the def itself is fine | n/a to the partial sum itself |
|  3 | construct an object → universal-property class?                                                         | no       | it's a concrete analytic sum, no universal property                                  | — |
|  4 | set-with-predicate → bundled substructure?                                                              | no       | the 3-predicate subtype is an index set for a sum, not an algebraic substructure     | — |
|  5 | real/metric/field-specific → weaken via typeclass hierarchy (real `s` → complex; reuse `LSeries`)?       | **yes**  | restate the partial sum as `LSeries (S.indicator (fun n ↦ Nat.card {I // absNorm I = n ∧ I.IsPrime})) s` with complex `s`, or as a prime-restricted `dedekindZeta` | unlocks the **entire** `Mathlib.NumberTheory.LSeries.*` + `NumberField.dedekindZeta` API: convergence, analytic continuation, the ζ_K pole / class-number-formula link, `LSeries_tendsto_sub_mul_nhds_one_*` |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | no categorical content                                                               | — |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive/ordered structure?                                            | no       | the index is prime ideals; `s` generalisation is #5 (ℝ→ℂ), already captured           | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (row 5).

- Proposed mathlib-idiomatic restatement: express the density numerator through
  mathlib's **complex** `LSeries` / `dedekindZeta` machinery — e.g. a
  prime-restricted Dirichlet series via `Set.indicator` coefficients — rather than
  a bespoke real `tsum` over a 3-predicate subtype.
- Cost: **EXPENSIVE** (a parallel complex-analytic development; the real-variable
  Chebotarev proof would have to be re-expressed or bridged).
- Mathlib downstream this enables: reuse of `Mathlib.NumberTheory.LSeries.*`
  (abscissa of convergence, analytic continuation), `NumberField.dedekindZeta`
  and `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (the ζ_K pole), and the existing
  `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg` — i.e. the
  density would compose with mathlib's analytic-NT stack instead of standing apart.
- Real mathematical improvement (not just "looks cooler"): **genuine but not
  clear-cut.** The complex form composes with the rest of mathlib's L-series
  theory; the real form is self-contained and lighter for an elementary proof.
  Which mathlib *wants* as the canonical "Dirichlet density of a set of primes"
  is exactly the open design question.

**Honesty note.** This is a real organisational question, not abstraction for its
own sake — but it is *not* a slam-dunk modernisation that should auto-flip the
verdict to YES-but-generalise. Mathlib might reasonably want the elementary real
form *as well*, or might insist density be built on `dedekindZeta`. That is a
maintainer judgment (Phase 7 → BORDERLINE).

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (`primeIdealZetaSum_def`); equation lemmas
introduce no typeclass-search paths or new definitional equalities beyond the
single `rfl` they expose.

(Parent-def note: `primeIdealZetaSum` is a plain `noncomputable def : ℝ` with no
instances, no coercions, no `@[reducible]`; were *it* assessed, all six risk rows
are NONE. The equation lemma is the controlled way to unfold it — itself a
mild point in favour of keeping the named def, see Phase 6.)

---

## Mathlib search-status: `Chebotarev.primeIdealZetaSum_def` / `primeIdealZetaSum`

[A] Lean-Finder       n/a — tool not available in this environment (no MCP handle); compensated with thorough grep (D) over the full mathlib tree.
[B] Loogle            n/a — `lean_loogle` not exposed as a tool here; intended patterns recorded: `Ideal.absNorm _ ^ (-_)`, `∑' _ : {_ // _ ∧ Ideal.IsPrime _ ∧ _ ≠ ⊥}, _`, `tsum (fun _ : Ideal _ => _ ^ _)`.
[C] LeanSearch        n/a — `lean_leansearch` not exposed here; intended NL queries: "Dirichlet density of a set of prime ideals", "partial Dedekind zeta sum over primes", "sum of N(p)^{-s} over prime ideals".
[D] Grep mathlib src  Ran extensively over `.lake/packages/mathlib/Mathlib/`:
      - `dedekindZeta|DedekindZeta|zetaSum` → only `NumberField.dedekindZeta` (complex `LSeries`), `dedekindZeta_residue`, `dedekindZeta_residue_def`, `tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
      - `[Dd]irichletDensity|[Aa]nalyticDensity|[Nn]aturalDensity|[Pp]rimeDensity` → **no hits** anywhere in mathlib.
      - `chebotarev|cebotarev|frobenius.*density` → **no hits**.
      - `tsum.*absNorm|absNorm.*\^.*\(-` and `absNorm.*: ℝ.*\^|absNorm.*rpow` → only unrelated discriminant-bound lines in `Discriminant/Basic.lean`. **No real-exponent prime-ideal power sum.**
      - `LSeries.*indicator|Set.indicator.*LSeries` → no prime-restricted indicator L-series.
[E] Name pattern      Grep for `primeIdealZetaSum`, `partialZeta`, `*Density` defs across mathlib `NumberTheory/` + `Analysis/` → the only `*Density` defs are probability/graph/Finset densities (`Probability/Density.lean`, `SimpleGraph/Density.lean`, `Data/Finset/Density.lean`) — **none** is an arithmetic density of primes.

Searched for both:
  - the user's current form (real `tsum` over the prime subtype) → **not in mathlib**.
  - the literature-standard / modern form (complex `LSeries`, `dedekindZeta`,
    prime-restricted Dirichlet series) → mathlib has `dedekindZeta` over **all**
    ideals (complex), but **no set-restricted / Dirichlet-density** object, and
    **no Chebotarev** machinery.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard complex form). The closest existing object is
`NumberField.dedekindZeta` — *complex, all-ideals, no set restriction, no
density* — i.e. a relative of the `S = univ` case, not this declaration.

Structural note: mathlib's own `dedekindZeta_residue_def : … := rfl`
(`DedekindZeta.lean:58`) is the **exact analog** of `primeIdealZetaSum_def` — an
equation lemma for a number-theory `def`. This confirms that such `rfl` equation
lemmas *do* belong in mathlib **when (and only when) their parent `def` does**:
they ride along with the def, never as an independent contribution.

---

## Call sites — `Chebotarev.primeIdealZetaSum_def`

Internal use count: **16** `rw [primeIdealZetaSum_def …]` occurrences (excluding
the definition at `Density.lean:55–56`), across **5** files.
External-to-file callers: **4** distinct files beyond `Density.lean`.

| Caller file:line                                   | Usage pattern (one-line excerpt)                                                         |
|----------------------------------------------------|------------------------------------------------------------------------------------------|
| `CebotarevDensity/Density.lean:99`                 | `simpa only [HasDirichletDensity, primeIdealZetaSum_def, tsum_empty, zero_div]`           |
| `CebotarevDensity/Density.lean:130,141,166,177,204,361,555` | `rw [primeIdealZetaSum_def, …]` — unfold before manipulating the underlying `tsum`       |
| `CebotarevDensity/FixedFieldDensity.lean:836,990`  | `rw [primeIdealZetaSum_def, primeIdealZetaSum_def, …]`                                   |
| `CebotarevDensity/Abelian.lean:1563`               | `primeIdealZetaSum_def S s ▸ tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _`  |
| `CebotarevDensity/CyclotomicNormResidue.lean:387,457,458` | `rw [primeIdealZetaSum_def, … hsummSig.tsum_sigma, primeIdealZetaSum_def, ← tsum_mul_left]` |
| `CebotarevDensity/Cyclotomic.lean:136,717,751,811` | `rw [primeIdealZetaSum_def, …]` / `rw [twistedPrimeSum, primeIdealZetaSum_def, Complex.ofReal_tsum, …]` |

Inline-derivation grep (was the equation re-derived elsewhere without using the lemma?):
  - (none) — every site that needs the unfolding uses `primeIdealZetaSum_def`. No
    one re-writes the raw `tsum` by hand, which is the point of the named def +
    equation lemma (it seals the unfolding behind one rewrite).

**Signal:** K = 16 internal uses across 5 files, zero inline re-derivation — this
is a **real, load-bearing project API**. The equation lemma is exactly the
"control the unfolding of a sealed `def`" pattern (Phase 2b exemption 1). It is
not dead code and not a bypassed wrapper. (This pushes the equation lemma's own
status firmly toward "keep" *within the project* — but does not by itself settle
whether the **parent object** belongs in **mathlib**, which is the density-design
question of Phase 4c.)

---

## Composition check (Phase 6)

Can `primeIdealZetaSum_def` be derived from mathlib in ≤3 chained calls?

Attempt 1: `primeIdealZetaSum_def` *itself* is `rfl` — trivially "composable" as a
definitional unfolding, but **only because `primeIdealZetaSum` exists as a project
def**. There is no mathlib object it unfolds *to*; mathlib has no
`primeIdealZetaSum`. So the question is vacuous for the equation lemma in
isolation: it cannot be "composed from mathlib" because the thing it unfolds is
not in mathlib.

Attempt 2 (the real question — the parent object): can `primeIdealZetaSum` /
`HasDirichletDensity` be assembled from mathlib primitives in ≤3 calls?
  - Mathlib decls available: `NumberField.dedekindZeta` (complex, all ideals),
    `Ideal.absNorm`, `tsum`, `Set.indicator`, `LSeries`.
  - Result: **fails** as a ≤3-call composition. Getting the *real, set-restricted*
    partial sum + the density *ratio limit* from `dedekindZeta` would require:
    restricting to primes, restricting to `S`, passing real→ via `Complex.ofReal`,
    and re-proving the density `Tendsto`/`limsup`/`liminf` theory — many steps with
    real reasoning between them (cf. the actual 800+-line `Abelian.lean`,
    `FixedFieldDensity.lean` developments). That is a development, not a composition.

Conclusion: **NOT-COMPOSABLE** (as a self-contained mathlib one-liner). The
equation lemma is `rfl`-trivial *given* the parent def, and the parent def is a
genuine new object relative to mathlib — neither is a ≤3-call mathlib composition.

---

## Verdict: `Chebotarev.primeIdealZetaSum_def`

**Category:** `BORDERLINE-needs-human` (inherited from the parent `def
primeIdealZetaSum`; verdict-inheritance rule for `rfl` glue lemmas).

**Evidence:**
- Literature search (Phase 3): the partial prime-ideal sum `Σ_{𝔭∈S}N𝔭^{-s}` is a
  **standard but unnamed auxiliary** of the Dirichlet-density definition; the
  *named* / modern analytic object is the **complex** Dedekind ζ / `LSeries`.
- Generality analysis (Phase 4): **STRICTLY NARROWER / NON-IDIOMATIC** (real,
  number-field, bespoke subtype) vs the complex-`LSeries` standard; modern-idiom
  reformulation available but **EXPENSIVE** and **not a clear win** (Phase 4c).
- Mathlib search (Phase 5): **not in mathlib** — no Dirichlet density, no
  Chebotarev, no real prime-ideal zeta sum; closest is `NumberField.dedekindZeta`
  (complex, all-ideals, no set restriction, no density).
- Composition check (Phase 6): **NOT-COMPOSABLE** — the parent object is a real
  development, not a ≤3-call assembly; the equation lemma is `rfl` only because the
  project def exists.

**Rationale.**

`primeIdealZetaSum_def` is a pure `:= rfl` equation lemma. By the verdict-
inheritance rule it cannot have an independent mathlibability status: it is
mathlib-worthy exactly when its parent `def primeIdealZetaSum` is, and it would be
PR'd *with* that def (mathlib's own `dedekindZeta_residue_def` is the precedent —
the `rfl` lemma ships alongside the `def`, never alone). So the decision collapses
to: **does mathlib want this particular partial-prime-zeta-sum object?**

That is a genuine judgment call, and it sits squarely in the reference's canonical
`BORDERLINE` case (Case 5 — `localZetaSum_chebotarev`, which this declaration
almost literally is). The object is *mathematically standard* (it is the numerator
of the Dirichlet density, in every ANT text) and *absent from mathlib* (no density
/ Chebotarev machinery exists) — which argues for inclusion. But three things hold
it back from a clean YES: (a) the literature never gives this partial sum its **own
name** — it is always inlined into the density definition, so the mathlib-canonical
contribution is plausibly `HasDirichletDensity` (the named concept), with the sum
as a `private`/local helper rather than a public `def`; (b) the **modern idiom is
complex `LSeries`/`dedekindZeta`** (already in mathlib), and whether mathlib wants
density built on that stack vs. this elementary real `tsum` is a maintainer
preference, not something the evidence decides; (c) re-idiomatising is **EXPENSIVE**
and per the skill, cost-driven shipping of the narrow form is itself a BORDERLINE
question, not a self-resolving downgrade. Meanwhile the call-site evidence (16 uses,
5 files, no inline re-derivation) shows the equation lemma is excellent **project**
API — but project-API quality is not the mathlib-canonicality question.

**Numbered questions (≤5):**

1. Should the mathlib-facing object be the **density concept** `HasDirichletDensity`
   (with the partial sum demoted to a `private`/inlined helper), rather than
   `primeIdealZetaSum` as a *public* named `def`? (The literature names the density,
   not the sum.)
2. Does mathlib want the Dirichlet density built on the **elementary real `tsum`**
   form (this project), or insist it be expressed through the existing **complex**
   `NumberField.dedekindZeta` / `Mathlib.NumberTheory.LSeries.*` machinery? (This is
   the EXPENSIVE-reformulation tradeoff — a maintainer call.)
3. Is the target generality **number fields** (current) or **global fields**
   (number + function fields)? mathlib may want the function-field case unified
   before accepting a number-field-only density `def`.
4. Is this development intended for upstreaming **as a whole** (the full Chebotarev-
   density package: `primeIdealZetaSum`, `HasDirichletDensity`, the sandwich API),
   in which case the equation lemma rides along automatically — or is it staying
   project-local? If project-local, no mathlib action is needed and the lemma simply
   stays.
5. If kept as a public `def`, is the name `primeIdealZetaSum` the one mathlib wants,
   given it is really a *prime-restricted partial Dedekind zeta sum* (the `S = univ`
   case is `log ζ_K + O(1)`)? A name tying it to `dedekindZeta` may be preferred.

**Next action:** user (mathlib-NT maintainer judgment) answers Q1–Q5. Most likely
resolutions:
  - Upstreaming the whole density package, real form accepted → the parent def +
    this `rfl` equation lemma go in **together** as `YES-add-as-is` (location
    `Mathlib/NumberTheory/NumberField/DirichletDensity.lean`, beside `DedekindZeta`),
    pending a `/generalise` pass on naming + the number-field-vs-global-field axis.
  - Maintainers want density on the **complex `LSeries`** stack → `YES-but-
    generalise-first` with reason MODERN-IDIOM (EXPENSIVE), restating against
    `dedekindZeta`/`LSeries`; the equation lemma is re-derived for the new def.
  - Staying project-local → drop from mathlib consideration; the lemma remains as
    (good) AINTLIB-internal API. No change.

---

## Next step

Surface questions Q1–Q5 to a mathlib number-theory maintainer. Because
`primeIdealZetaSum_def` is a `:= rfl` glue lemma, do **not** assess or PR it
independently — its fate is bound to `def primeIdealZetaSum`; resolve the parent's
BORDERLINE (real-`tsum` vs complex-`LSeries` density, naming, base-field
generality, upstream-as-a-whole), and the equation lemma follows automatically.
