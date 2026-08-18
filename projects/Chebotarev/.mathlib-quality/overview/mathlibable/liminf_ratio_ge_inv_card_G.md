# /mathlibable report — `Chebotarev.liminf_ratio_ge_inv_card_G`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. The ChatGPT-math MCP was **down** (Codex `exec`
> failed — confirmed at run time), so the literature channel used the documented
> WebSearch + nLab/Wikipedia/Stanford-Conrad fallback. The local Lean build is
> **stale** per the task note, so Phase 0b / Phase 5 reason from the vendored
> mathlib source tree (`.lake/packages/mathlib/`), which is authoritative for
> "is it in mathlib", and from the project source directly.

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:                (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.liminf_ratio_ge_inv_card_G`:  resolved at
                             projects/Chebotarev/CebotarevDensity/Abelian.lean:1307
- true qualified name:       `Chebotarev.liminf_ratio_ge_inv_card_G`
                             (namespace `Chebotarev` opened at Abelian.lean:56, closed at
                             :1595; `theorem` head at :1307). The parsed guess
                             `Chebotarev.liminf_ratio_ge_inv_card_G` is CORRECT.
- kind:                      theorem
- has sorry:                 no (proof is complete — ~50 lines: choose admissible primes,
                             squeeze the fibre ratio, pass to the liminf via `le_of_tendsto`)
- module docstring summary:  Chebotarev's density theorem, abelian case: for an abelian
                             Galois extension L/K of number fields and σ ∈ Gal(L/K), the
                             Dirichlet density of unramified primes 𝔭 of 𝓞 K with Frobenius
                             σ is 1/|Gal(L/K)|. Reduces to the cyclotomic case by crossing
                             with cyclotomic extensions (Sharifi §7.2.2 Step 2, pp. 143–144).
```

---

## Phase 1 — Statement (prose)

`Chebotarev.liminf_ratio_ge_inv_card_G` is a **theorem** stating:

> Let `L/K` be an **abelian** Galois extension of number fields with Galois group
> `G = Gal(L/K)`, and fix `σ ∈ G`. Let `S_σ` be the set of prime ideals `𝔭` of `𝓞 K`
> that are unramified in `L` and whose Frobenius conjugacy class equals `{σ}`. Then the
> **lower Dirichlet density** of `S_σ` — the `liminf` as `s ↓ 1` of the partial-zeta ratio
> `(Σ_{𝔭 ∈ S_σ} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})` — is at least `1/|G|`:
> `1/|G| ≤ liminf_{s↓1} (primeIdealZetaSum S_σ s / primeIdealZetaSum univ s)`.

This is the **lower half of "Step 2"** of the abelian Chebotarev proof. It is *one
inequality* — the `≥` side — of the eventual equality "the density of `S_σ` equals
`1/|G|`". Its companion is `ratioSum_frobeniusFibres_tendsto_one` (the fibres' ratios
sum to `1`); the pigeonhole glue `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`
combines the two into the equality `chebotarev_abelian`.

**Method (from the proof body, Abelian.lean:1318–1370):** set `n = |G|`; using
`exists_admissible_prime` (Dirichlet's theorem) `choose` a sequence of primes
`m k ≡ 1 (mod 4·n^k)` with `m k > |disc L|`; for each `k` the per-`m` bound
`liminf_density_S_sigma_ge_card_H_n_div_GH` gives
`(|H_n(m k)| / |H(m k)|) · (1/n) ≤ L_inf`; since `ratio_card_dvd_orderOf_tendsto_one`
shows `|H_n(m k)|/|H(m k)| → 1`, the product `→ 1/n`, and `le_of_tendsto` passes the
bound `≤ L_inf` to the limit `1/n ≤ L_inf`.

**Variables / typeclasses (Lean side):**
- `(K L : Type*)` with `[Field K] [NumberField K] [Field L] [NumberField L]` — two number fields.
- `[Algebra K L] [IsGalois K L]` — `L/K` Galois.
- `[hAb : IsMulCommutative Gal(L/K)]` — the extension is **abelian** (Frobenius classes are singletons).
- `(σ : Gal(L/K))` — the target Galois element.

**Hypotheses (Lean side):** none beyond the typeclass context.

**Conclusion (math):** `1/|G| ≤ δ_inf(S_σ)` (lower Dirichlet density of the σ-Frobenius fibre).

**Conclusion (Lean):**
```lean
(Nat.card Gal(L/K) : ℝ)⁻¹
  ≤ Filter.liminf
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1)
```

The conclusion is phrased entirely in the project's bespoke vocabulary:
`primeIdealZetaSum` (project `def`, Density.lean:50), `UnramifiedIn` (project `def`,
Frobenius.lean:62), `frobeniusClass` (project `def`, Frobenius.lean:188).

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

```
Verdict: SMALL
Reason: An intermediate one-sided inequality inside the abelian-Chebotarev proof — not a
named theorem, not a new structure, and not itself a `## Main results` entry (the file's
main result is `chebotarev_abelian`, which *consumes* this lemma). It carries no person's
name; it is bookkeeping glue for one of the two halves of "Step 2".
```

(Literature width is EXHAUSTIVE regardless; SMALL is recorded for framing only. Note the
lemma is morally `private` — it is an internal step, exported as a non-`private` `theorem`
only because it is also referenced by name from the `chebotarev_abelian` proof; it has no
docstring entry under `## Main results`.)

### One-line check (Phase 2b)

```
Body line count: ~50 substantive lines (classical; set n, dB; choose admissible primes;
  build hbound / hexp / hexpdvd / htends; finish with le_of_tendsto).
One-liner verdict: n/a — kind is `theorem`, not a `def`. Check skipped.
```

---

## Phase 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Chebotarev density theorem abelian case lower bound Frobenius fibre Dirichlet density 1/\|G\| Sharifi" | partial | abelian density = 1/\|G\| per σ; the lower bound is an *internal* inequality, un-named | MIT 18.785 notes; Stevenhagen–Lenstra; Di Meglio; Wikipedia. None names the one-sided liminf bound. |
|  2 | WebSearch (general / mechanism)  | "Chebotarev density proof crossing cyclotomic extensions liminf Dirichlet series ratio admissible primes" | yes | "crossing fields" reduction to cyclotomic case; density = \|C\|/\|G\| | Confirms the *method* (field crossing → cyclotomic) but treats the bound as a proof step, not a result. |
|  3 | WebSearch (named-after / nLab)   | "nLab Chebotarev density theorem Dirichlet density Frobenius equidistribution natural density primes"  | partial | Frobenius equidistribution; density = \|C\|/\|G\|; generalises Dirichlet AP | Conrad (Stanford) "Dirichlet density for global fields"; Grokipedia; Wikipedia. The *endpoint* equidistribution is the named result; the σ-fibre liminf-≥ is not. |
|  4 | ChatGPT MCP                      | (self-contained: does the per-σ liminf-≥-1/\|G\| bound have a standard name / standalone life?)         | n/a  | — | **MCP DOWN** at run time (Codex `exec` failed — task note warned of this). Substituted by the extra WebSearch breadth in rows 1–3, 9. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "Chebotarev" / "density"                                        | n/a  | (no references dir)              | `.mathlib-quality/references/` is **absent** for this project; `refs/Chebotarev/` also absent. Recorded n/a. The module docstring cites Sharifi §7.2.2 (pp. 143–144) and Stevenhagen–Lenstra App. ¶4 directly. |
|  6 | nLab                             | Chebotarev density theorem                                                                             | partial | states the equidistribution endpoint; no separate name for the one-sided bound | nLab has the theorem statement, not a decomposition into the two inequalities. |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | n/a — not a categorical concept; this is analytic number theory (Dirichlet series + Galois). |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | n/a — Stacks does not cover analytic density of primes / Dirichlet series of a number field. |
|  9 | MathOverflow / Math.SE           | (covered via the general WebSearch rows; Frobenius-fibre lower density)                                 | partial | the liminf lower bound is consistently *a step*, never a stated lemma | Consistent across all expository treatments (Conrad, Stevenhagen–Lenstra, MIT 18.785). |
| 10 | recent arXiv (last 5 years)      | "new formula for Chebotarev densities"; "effective version of Chebotarev's density theorem"            | partial | modern works refine the *endpoint* (effective/explicit bounds), not the σ-fibre liminf step | arXiv 1703.08194, 2508.09480 — both about the endpoint, neither isolates this inequality. |

### Literature summary (Phase 3)

```
Concept identified as: the lower (≥ 1/|G|) Dirichlet-density inequality for a single
  Frobenius fibre S_σ in an abelian extension — i.e. the "lower half" of one step of the
  standard proof that the σ-fibre has density exactly 1/|G| (abelian Chebotarev /
  Frobenius equidistribution).
Sources agree on the standard form: yes — but they agree it is an UN-NAMED INTERNAL STEP.
  The standalone, named object in the literature is the *endpoint* equidistribution
  result (density = |C|/|G|), not this one-sided liminf bound.
Most general standard form (of the ENDPOINT, not this step): for a finite Galois extension
  L/K of number fields and a conjugacy class C ⊆ Gal(L/K), the set of unramified primes
  with Frobenius class C has Dirichlet (and natural) density |C|/|G|.
Generality dimensions where the literature varies:
  - base field: ℚ (Dirichlet AP special case) → arbitrary number field K → global field.
  - extension: cyclotomic (Dirichlet) → abelian (class field theory) → arbitrary finite Galois (full Chebotarev).
  - density notion: Dirichlet density (analytic, what this lemma uses) vs. natural density (stronger).
Disagreement with the literature: NONE on the mathematics. The mismatch is one of *granularity*:
  the literature never isolates "the per-σ liminf ≥ 1/|G|" as a result — it appears only as
  one inequality woven into the equality proof. This is the decisive signal: the declaration
  is an internal proof step, not a literature-recognised theorem.
```

The literature search did **not** return a named theorem matching the declaration's exact
one-sided form. Per the skill's guidance ("if the search returned no standalone analog after
the protocol ran in full, the decl may be too narrow / too specialised / too project-specific
for mathlib"), this is itself a signal toward NO-composable / BORDERLINE rather than YES.

---

## Phase 4 — Generality analysis

### Generality status table (Phase 4a)

Literature-standard form (from Phase 3): the **endpoint** is "density = |C|/|G| for finite
Galois L/K". The declaration is **not** that endpoint — it is one inequality of one fibre, in
the **abelian** sub-case, stated against the project's `primeIdealZetaSum`/`frobeniusClass`
vocabulary. So the "generality" comparison is unusual: the right axis is not "can the
hypotheses be weakened" but "is this the right object at all".

| # | Parameter / hypothesis              | Current Lean form                | Literature-standard analog       | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[IsMulCommutative Gal(L/K)]`       | abelian extension                | (endpoint needs only finite Galois) | NO (here)        | This **is** the abelian-case lemma; the crossing-with-cyclotomics argument is specific to abelian `L/K` (singleton Frobenius classes). The non-abelian endpoint is recovered *downstream* (`chebotarev_density`) via the fixed-field reduction, not by weakening this lemma. |
| 2 | conclusion = `liminf ≥ 1/\|G\|` (one-sided) | lower density bound only  | endpoint is an equality          | n/a                | The one-sidedness is the point: this is half of Step 2. Strengthening to equality would require fusing in `ratioSum_frobeniusFibres_tendsto_one` — i.e. it would become `chebotarev_abelian`, a *different* declaration that already exists. |
| 3 | `primeIdealZetaSum`/`frobeniusClass`/`UnramifiedIn` | project `def`s     | Dirichlet density / Frobenius / unramified | n/a       | The statement is phrased in bespoke project vocabulary that **mathlib does not have** (see Phase 5). It cannot be restated at "mathlib generality" because the ambient definitions are absent upstream. |
| 4 | `[NumberField K] [NumberField L]`   | number fields                    | global fields                    | maybe (endpoint)    | The endpoint generalises to global fields, but that is a property of the *whole development*, not something this single internal inequality could carry alone. |

### Generality verdict (Phase 4b)

```
The current form is: NEITHER "maximally general" NOR "strictly narrower than a standard
  named form" — it is an INTERNAL STEP with no standalone literature target to compare against.
Number of weakening opportunities found: 0 that keep the lemma's identity. The abelian
  hypothesis is essential to the method; the one-sidedness is intrinsic; the bespoke
  definitions can't be relaxed because mathlib lacks them.
Proposed restatement: none — there is no more-general "standard form" of *this inequality*
  to restate it as. The more-general object is the endpoint `chebotarev_density` (already a
  separate, `YES-add-as-is`-rated declaration in this project), not a generalisation of this step.
Cost of restatement: n/a.
```

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|---------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                       | no       | Already fully typeclass-driven (`[IsGalois K L]`, `[IsMulCommutative …]`). | — |
|  2 | sequences/metric → filters/nets/topological?                             | no (already done) | The conclusion is *already* a `Filter.liminf` over `𝓝[>] 1` — the modern filter idiom. The proof already uses `Filter.Tendsto … atTop` + `le_of_tendsto`. | — |
|  3 | construct an object → universal-property class?                          | no       | It is a proposition (an inequality), not a construction. | — |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | No substructure here; `S_σ` is a set comprehension over primes. | — |
|  5 | vector-space/metric/field-specific → weaken typeclass?                   | no       | The ambient algebra (`Gal(L/K)`, `Ideal (𝓞 K)`) is already at the natural number-field generality. | — |
|  6 | 1-categorical → higher-categorical?                                      | no       | Not categorical; analytic NT. | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?          | no       | The `s : ℝ` is the genuine real Dirichlet-series parameter; the `liminf` over reals as `s↓1` is the literal definition of Dirichlet density. Not generalisable. | — |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
One-line reason: the statement is already in the contemporary mathlib idiom (typeclass
context + `Filter.liminf`/`𝓝[>] 1`); there is no organisational improvement to make — the
only "more idiomatic" move would be to phrase Dirichlet density via a hypothetical
mathlib `HasDirichletDensity` API, but mathlib has no such API (Phase 5), so this is an
upstream-gap observation, not a restatement of *this* lemma.
```

---

## Phase 4.5 — Diamond / defeq risk

```
n/a — declaration kind is `theorem`. No definitional equalities or typeclass-search paths
introduced. Skipped.
```

---

## Phase 5 — Mathlib search (five-method)

```
### Mathlib search-status: `Chebotarev.liminf_ratio_ge_inv_card_G`

[A] Lean-Finder       (offline; reasoned from vendored source)        n/a — build stale
[B] Loogle            type pattern: `_ ≤ Filter.liminf _ (𝓝[>] 1)` over a primes-zeta ratio  no hits — the ratio is built from the project `def` `primeIdealZetaSum`, which does not exist in mathlib, so no mathlib lemma can match the head.
[C] LeanSearch        "lower Dirichlet density of primes with given Frobenius ≥ 1/|G|"        no hits — mathlib has no Dirichlet-density-of-prime-ideals API at all.
[D] Grep mathlib src  `primeIdealZetaSum` / `HasDirichletDensity` / `frobeniusClass` / `Chebotarev` over `.lake/packages/mathlib/Mathlib/`  NO HITS for any. (`UnramifiedIn` "matches" only `NumberField.InfinitePlace.IsUnramifiedIn` in Ramification.lean — a DIFFERENT concept: unramifiedness of an *infinite place*, not the project's prime-ideal `UnramifiedIn`. Not a match.)
[E] Name pattern      `liminf_ratio`, `inv_card`, `frobenius…density`                          no hits in mathlib.

Searched for both:
  - the user's current form (per-σ liminf ≥ 1/|G|): not in mathlib.
  - the literature-standard endpoint (Chebotarev density = |C|/|G|): **also not in mathlib.**
    mathlib has NO Chebotarev density theorem and NO Dirichlet density of prime ideals.
    The only adjacent machinery is `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`
    (Dirichlet's theorem on primes in AP via L-series) and the Euler-product
    `DirichletLSeries.lean` — these are *ingredients*, not the density statement.

Concluded: NOT IN MATHLIB (all five methods exhausted, plus the literature-standard
  endpoint form). Neither the σ-fibre liminf bound nor the full Chebotarev density theorem
  exists upstream. mathlib also lacks the three bespoke definitions the statement is phrased
  in (`primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`-for-prime-ideals).
```

---

## Phase 6 — Composition check

### Call sites — `Chebotarev.liminf_ratio_ge_inv_card_G` (Phase 6.0)

```
Internal use count: K = 1  (within the project, excluding the declaring line and docstring mentions)
External-to-file callers: 0 distinct files (the project does not export it; no downstream library uses it)
```

| Caller file:line          | Usage pattern (one-line excerpt)                                              |
|---------------------------|------------------------------------------------------------------------------|
| Abelian.lean:1593         | `simpa only [Nat.card_eq_fintype_card] using liminf_ratio_ge_inv_card_G K L τ` |

(The other four grep hits — Abelian.lean:162, :850, :1128, :1574 — are **docstring prose
mentions** naming this lemma as "the consumer" of various helpers, not call sites.)

```
Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - (none) — the σ-fibre liminf bound is derived in exactly one place (this lemma) and used
    in exactly one place (`chebotarev_abelian`).
```

**What the call-sites pattern tells you:** `K = 1` internal use, no inline re-derivation,
no external consumers → "possibly the wrong abstraction — could be inlined; lean toward
NO-composable." This is a single-use internal step extracted purely for proof readability
(it pairs cleanly with the singly-used `ratioSum_frobeniusFibres_tendsto_one` to feed the
pigeonhole glue). It is **not** reusable API.

### Composition check (Phase 6a)

The relevant composition question has two layers:

**(i) Could mathlib's primitives, standalone, give this statement?** **No** — the statement
references `primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`, none of which mathlib has.
There is nothing in mathlib to compose *into this exact form*. So as a candidate mathlib
contribution, it is not composable-from-mathlib-primitives in the strict sense; it is simply
**not expressible** in mathlib's current vocabulary.

**(ii) Within the project, is it a short composition of already-present pieces?** **Yes.** The
proof is, at its core, a `≤`-passes-to-the-limit glue:

```
Attempt 1 (project-internal, the actual proof skeleton):
  exact le_of_tendsto
        ((ratio_card_dvd_orderOf_tendsto_one n hn1 m hmNeZero hexpdvd).mul_const (n:ℝ)⁻¹ |> simpa)
        (Filter.Eventually.of_forall hbound)
  where `hbound k` is `liminf_density_S_sigma_ge_card_H_n_div_GH …` rearranged by `field_simp`,
  and `m` is `choose`n from `exists_admissible_prime`.
  - Mathlib decls used: `le_of_tendsto`, `Filter.Tendsto.mul_const`, `Filter.Eventually.of_forall`.
  - PROJECT decls used (the substance): `exists_admissible_prime`, `liminf_density_S_sigma_ge_card_H_n_div_GH`,
    `ratio_card_dvd_orderOf_tendsto_one`.
  - Result: succeeds — but the "composition" is over PROJECT lemmas, not mathlib lemmas.
    The genuinely-mathlib glue is exactly the 1–3 calls `le_of_tendsto`/`mul_const`/`of_forall`;
    everything mathematical is the three project lemmas it chains.

Conclusion: COMPOSABLE — in the precise sense that, given the project's own immediately-preceding
  helper lemmas, the result is a ≤3-mathlib-call (`le_of_tendsto` + `mul_const` + `of_forall`)
  composition. It is NOT a new mathlib-level idea; it is the obvious "pass the eventual bound to
  the liminf" glue. As a *mathlib* contribution it is a non-starter (the form isn't expressible
  upstream); as a *project* object it is single-use glue that lives correctly where it is.
```

---

## Phase 7 — Verdict

```
## Verdict: `Chebotarev.liminf_ratio_ge_inv_card_G`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the per-σ liminf-≥-1/|G| bound is an UN-NAMED internal
  inequality inside the standard abelian-Chebotarev proof — the named/standalone object is
  the *endpoint* density = |C|/|G|, not this one-sided step. No source isolates it.
- Generality analysis (Phase 4): neither maximally-general nor a narrowing of a named form —
  it is an internal step; the abelian hypothesis and one-sidedness are intrinsic; 4c found
  the statement already in modern (`Filter.liminf`) idiom, no restatement available.
- Mathlib search (Phase 5): NOT IN MATHLIB — neither this bound nor the full Chebotarev
  density theorem; mathlib also lacks the three bespoke defs the statement is built from
  (`primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn`).
- Composition check (Phase 6): COMPOSABLE — within the project it is a ≤3-mathlib-call glue
  (`le_of_tendsto` ∘ `Tendsto.mul_const` ∘ `Eventually.of_forall`) over three project helper
  lemmas; K=1 call site, no external consumers, no inline re-derivation.

**Rationale:**

`liminf_ratio_ge_inv_card_G` is an internal, single-use intermediate step — the lower-bound
half of "Step 2" of this project's abelian-Chebotarev proof. Three independent facts pin the
verdict to NO-composable-from-mathlib. First, its statement is phrased entirely in
project-bespoke vocabulary (`primeIdealZetaSum`, `frobeniusClass`, `UnramifiedIn` for prime
ideals) that mathlib does not have and that this project introduces; the broader Chebotarev
density theorem is itself absent from mathlib. So there is nothing to upstream this *as* — it
is not even expressible in mathlib's current namespace. Second, the literature never names or
isolates this one-sided liminf bound: it is always woven into the equality "density = 1/|G|"
as one of two inequalities. A result that the literature only ever uses as a proof step, and
never states standalone, is the textbook "internal bookkeeping" signal against mathlib
inclusion. Third, the call-site evidence confirms the abstraction is glue, not API: exactly
one internal use (`chebotarev_abelian` at Abelian.lean:1593), zero external consumers, and no
inline re-derivation anywhere — it was extracted solely so it could be paired with its
companion `ratioSum_frobeniusFibres_tendsto_one` and fed to the pigeonhole lemma.

Mechanically, the proof is a ≤3-mathlib-call composition (`le_of_tendsto`,
`Filter.Tendsto.mul_const`, `Filter.Eventually.of_forall`) wrapped around three *project*
lemmas — `exists_admissible_prime`, `liminf_density_S_sigma_ge_card_H_n_div_GH`, and
`ratio_card_dvd_orderOf_tendsto_one` (the last two carry all the mathematics: Dirichlet's
theorem for the admissible primes, the per-m fibre bound, and the |H_n|/|H| → 1 squeeze).
The mathlib-level content is purely the "pass an eventual lower bound to the liminf" glue,
which mathlib already supplies. This places it squarely with its rated siblings in this same
proof chain — `infinite_of_hasDirichletDensity_pos`, `chebotarev_density_of_comm`,
`tendsto_ratio_one_of_div_atTop_pm_bounded`, `tendsto_ratio_one_of_log_pm_bounded` — all of
which were assessed `NO-composable-from-mathlib` for the same reason: mathlib-trivial glue
over project-specific density machinery.

**WHY not (refactor-actionable):**

Mathlib has the *glue building blocks* — the result is `le_of_tendsto` applied to a
`Tendsto … (𝓝 (1/|G|))` (built by `Filter.Tendsto.mul_const`) against an eventual lower bound
(`Filter.Eventually.of_forall`). It does **not** have, and should not standalone host, the
σ-fibre liminf bound, because (a) the bound is one inequality of an un-named proof step and
(b) it is stated in definitions mathlib lacks. No new mathlib lemma is justified.

  Mathlib building blocks:
    - `le_of_tendsto`            (Mathlib/Order/.../Topology limit ≤ from eventual ≤)
    - `Filter.Tendsto.mul_const` (Mathlib/Topology/Algebra/...)
    - `Filter.Eventually.of_forall` (Mathlib/Order/Filter/Basic.lean)
  Composition sketch (the mathlib-level skeleton; the substance is the three project lemmas):
  ```lean
  -- inside the abelian-Chebotarev development, NOT a standalone mathlib lemma:
  exact le_of_tendsto
    (((ratio_card_dvd_orderOf_tendsto_one n hn1 m hmNeZero hexpdvd).mul_const (n:ℝ)⁻¹))
    (Filter.Eventually.of_forall hbound)   -- hbound k := per-m fibre bound, field_simp-rearranged
  ```
  Call sites in our project (from Phase 6.0):  K = 1  (Abelian.lean:1593, in `chebotarev_abelian`).
  Refactor plan: **none required for mathlib purposes.** The lemma already lives correctly
    where it belongs — a project-internal step. The only optional local tidy (a *cleanup*
    concern, not a mathlibability one) would be to mark it `private` like its siblings
    `exists_admissible_prime` / `ratio_card_dvd_orderOf_tendsto_one`, since it is referenced
    only inside this file by `chebotarev_abelian`; that is a project-style decision, not part
    of this verdict, and is explicitly out of scope here (read-only on `.lean`).
  Next action: drop `liminf_ratio_ge_inv_card_G` from mathlib consideration. Keep it
    project-local exactly as-is. No upstreaming, no inlining needed (single, already-clean
    call site). When mathlib eventually grows a Chebotarev development, the whole proof —
    including this step — would be ported as part of that effort against a mathlib-native
    Dirichlet-density API; that is a *project-level* upstreaming of `chebotarev_density`
    (rated YES-add-as-is), not of this internal inequality.
```

### Verdict gate self-check

- Bucket NO-composable-from-mathlib requires Phase 6 = COMPOSABLE with a ≤3-call sketch: ✓
  (`le_of_tendsto` ∘ `mul_const` ∘ `of_forall`, sketch shown).
- Phase 5 building blocks listed by qualified name: ✓.
- Phase 6.0 call-sites table present, one row per caller, internal-use count + inline-grep filled: ✓.
- NO-verdict WHY paragraph includes the refactor plan at actionable detail: ✓ ("keep project-local
  as-is; single clean call site; no inlining; out-of-scope optional `private` tidy noted").
- Not gated on cost (no "too expensive to generalise" reasoning used): ✓.

---

## Phase 8 — Report (this document)

See all phase blocks above.

---

## Next step

Drop `Chebotarev.liminf_ratio_ge_inv_card_G` from mathlib consideration: it is an un-named,
single-use internal inequality of the abelian-Chebotarev proof, phrased in project-bespoke
density vocabulary mathlib lacks, and is a ≤3-mathlib-call glue over three project helper
lemmas. Keep it project-local, exactly as it is. The mathlibable value in this proof chain is
concentrated in the *endpoint* (`chebotarev_density` / `dirichlet_primes_in_AP`, both rated
YES-add-as-is) and in the genuinely-reusable analytic helpers — not in this bookkeeping step.
