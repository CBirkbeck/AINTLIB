# /mathlibable report — `Chebotarev.primeIdealZetaSum`

> Step-9 overview mathlibable assessment. Read-only on `.lean`; this is the sole written artifact.
> Environment note: local Lean build is stale, ChatGPT-math MCP was down; literature via WebSearch +
> Wikipedia + Conrad handout; mathlib search via grep over `.lake/packages/mathlib` + Loogle web UI
> (the `lean_loogle`/`lean_leansearch` MCP indices were not available in this thread). The grep over
> the actual pinned mathlib source is authoritative for the "is it there" question.

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (stale local build per task brief; reasoning from source statement)
- decl `Chebotarev.primeIdealZetaSum`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Density.lean:50`
- kind:                      `def` (noncomputable, `@[expose] public section`)
- has sorry:                 no (it is a definition — a `tsum`)
- module docstring summary:  Dirichlet density of a set `S` of prime ideals of `𝓞 K` for a number field `K`.

True qualified name confirmed: namespace `Chebotarev` (Density.lean:44) ⇒ **`Chebotarev.primeIdealZetaSum`**
(the parsed guess was correct).

---

### Statement (Phase 1)

`Chebotarev.primeIdealZetaSum` is **a definition** of the partial Dirichlet series

$$\;f_S(s) \;=\; \sum_{\substack{\mathfrak p \in S \\ \mathfrak p \text{ prime},\ \mathfrak p \neq 0}} N(\mathfrak p)^{-s},$$

the sum (an unconditional `tsum`) of $N(\mathfrak p)^{-s}$ over the nonzero **prime** ideals $\mathfrak p$
of the ring of integers $\mathcal O_K$ of a number field $K$ that lie in a given set $S$ of ideals,
where $N = $ `Ideal.absNorm` is the absolute norm and $s\in\mathbb R$. With $S = \mathrm{univ}$ this is
the prime-indexed sum whose value is asymptotic to $\log\frac1{s-1}$ as $s\downarrow 1$; it serves as
both the **numerator** ($S$ arbitrary) and the **denominator** ($S=\mathrm{univ}$) of the Dirichlet
density ratio
$\delta(S) = \lim_{s\to1^+} f_S(s)/f_{\mathrm{univ}}(s)$ (defined just below it as `HasDirichletDensity`).

Variables / typeclasses (Lean side):
- `{K : Type*} [Field K] [NumberField K]` — a number field (its ring of integers `𝓞 K` carries the ideals).
- `(S : Set (Ideal (𝓞 K)))` — the set of ideals to restrict to.
- `(s : ℝ)` — the real exponent variable.

Hypotheses: none (total definition; summability/positivity are separate lemmas right below it).

Conclusion (math): the real number $\sum_{\mathfrak p\in S,\ \text{prime},\ \neq0} N(\mathfrak p)^{-s}$.

Conclusion (Lean): `ℝ`. Body:
```lean
∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
```

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a **new named mathematical object** (the partial / prime-restricted Dirichlet-series sum)
and the foundational definition of the whole Chebotarev-density development — listed first under
`## Main definitions` in the module docstring (Density.lean:27) and the carrier of the project's
`δ_S` notion. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (a `tsum` over a three-conjunct subtype with the `absNorm^(-s)`
summand). **MULTI-LINE** — not a one-liner. The body carries genuine mathematical content (the index
set `S ∩ {prime} ∩ {≠⊥}` and the summand), so the one-liner negative-signal exemption table does not
apply. No bias toward NO from Phase 2b.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------|-------|
| 1  | WebSearch (specific form)        | "Dirichlet density prime ideals partial zeta function sum N(p)^{-s} number field"              | yes  | $\delta(M)=\lim_{s\to1^+}\big[\sum_{\mathfrak p\in M}N\mathfrak p^{-s}\big]/\big[\sum_{\mathfrak p}N\mathfrak p^{-s}\big]$ | exact match for our numerator/denominator; also gives the $\log\frac1{s-1}$ variant of the denominator |
| 2  | WebSearch (general form)         | "partial Dedekind zeta function sum over prime ideals in a set standard definition"           | yes  | full ζ_K is over **all** nonzero ideals; "Dedekind partial zeta function" $\zeta_{K,A}(s)=\sum_{I\in[A]}N(I)^{-s}=\prod_{P\in A}(1-N(P)^{-s})^{-1}$ | "partial zeta" is normally over a **subset of ideals/ideal classes**, with the Euler product over the corresponding primes; our object is the prime-sum (log of that), the standard density numerator |
| 3  | WebSearch (named-after / aliases)| "Neukirch Stevenhagen Dirichlet density prime ideals Np^{-s} real s tends to 1"               | yes  | same δ(M) formula; sources = Stevenhagen–Lenstra *Chebotarëv…*, Neukirch, Conrad "Dirichlet density for global fields" | confirms the **real** $s\to1^+$ convention is the one used for density; confirms generality extends to global fields |
| 4  | ChatGPT MCP                      | (3-part: standard name? generality? real vs complex s?)                                        | n/a  | — MCP server down (Codex exec failed); fell back to Wikipedia + Conrad title + source docstrings | brief warned MCP may be down; recorded as n/a with reason |
| 5  | Local references                 | grep `.mathlib-quality/references/`                                                            | n/a  | directory absent for this project                                                | recorded n/a |
| 6  | nLab                             | "Dirichlet density"                                                                            | no   | nLab has no dedicated *Dirichlet density* page (HTTP 404)                         | concept is classical ANT, not categorical; n/a-ish |
| 7  | nCatLab (if categorical)         | —                                                                                              | n/a  | not a categorical concept                                                         | — |
| 8  | Stacks Project (if alg geom)     | —                                                                                              | n/a  | not an algebraic-geometry/scheme concept (it is an analytic-number-theory series)| — |
| 9  | MathOverflow / Math.SE           | covered transitively via the WebSearch hits (Conrad handout, Leiden theses)                   | yes  | consistent δ(M) definition; partial sum written inline, no special symbol        | the numerator sum is consistently written **inline**, not given a standalone name |
| 10 | recent arXiv (last 5 yrs)        | "S has positive Dirichlet density" (arXiv 2603.27472, 2009.10431, 2307.12175)                  | yes  | same definition in current use; restricted-ramification / CSP papers all use the prime-sum-ratio | confirms the formulation is live and unchanged in 2020s literature |

Protocol pass check: WebSearch ran 3 distinct queries at different generality levels ✓; ChatGPT MCP
attempted, recorded n/a with reason (server down) ✓; local refs checked (absent) ✓; nLab checked ✓;
Stacks/nCatLab/MO/arXiv each checked or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: the **partial sum in the Dirichlet-density ratio** — i.e. $\sum_{\mathfrak p\in S}N(\mathfrak p)^{-s}$
over (nonzero) prime ideals. It is the (logarithm of the) prime part of the **Dedekind partial zeta
function** $\zeta_{K,A}$; equivalently the number-field analogue of the **prime zeta function**
restricted to the set $S$.

Sources agree on the standard form: **yes** — every source (Wikipedia *Dirichlet density*,
Stevenhagen–Lenstra, Conrad, the arXiv papers) writes the density as the ratio of exactly this
prime-sum over the all-primes sum, with **real** $s\to1^+$.

Standard name of its own: **none.** Across all channels the numerator $\sum_{\mathfrak p\in S}N\mathfrak p^{-s}$
is written **inline**; it is not given a standalone symbol/name in the literature. (The *full* sum over
all nonzero ideals is the Dedekind zeta; the prime sum is "the numerator".) So the project's name
`primeIdealZetaSum` is a sensible, descriptive coinage rather than a fixed textbook term.

Most general standard form: for **global fields** (number fields *and* function fields), the density
numerator is $\sum_{v\in S} q_v^{-s}$ over places/primes $v$ with residue cardinality $q_v$. Our Lean
form fixes the number-field case (residue cardinality = `Ideal.absNorm`).

Generality dimensions where the literature varies:
- **Ground field:** number field $\to$ arbitrary global field (Conrad). Most general = global field.
- **Variable:** real $s\downarrow1$ is the standard *density* convention; complex $s$ with $\mathrm{Re}\,s>1$
  is the standard convention for the *zeta function as an analytic object*. For density specifically the
  literature uses real $s$ — our form matches.
- **Index:** over a set of **primes** (density numerator) vs over a set of **all ideals/ideal classes**
  (partial zeta $\zeta_{K,A}$). Our form is the prime-set version, correct for density.

---

## PHASE 4 — Generality analysis

Literature-standard form (Phase 3): density numerator over a set of primes of a **global field**,
real $s\to1^+$.

### 4a. Generality status table

| # | Parameter / hypothesis                  | Current Lean form                          | Literature-standard form               | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------|--------------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | `[Field K] [NumberField K]`              | number field                               | global field (number OR function field)| **yes** (in principle) | Density theory runs over all global fields; but mathlib has **no** developed "global field / its primes with residue norm" zeta infrastructure (no function-field side, no `Ideal.absNorm` analogue over $\mathbb F_q[t]$ rings in this API). Generalising now would be EXPENSIVE and has no mathlib substrate to land on. |
| 2 | `(S : Set (Ideal (𝓞 K)))`               | set of ideals (intersected with primes)    | set of primes                          | no                  | the right index handle; intersecting with `IsPrime ∧ ≠⊥` inside is the standard "set of primes" presentation. |
| 3 | summand `(absNorm 𝔭)^(-s)`, `s : ℝ`      | real exponent                              | real $s$ for density (complex for the analytic zeta) | no (for this purpose) | density is *defined* with real $s\to1^+$; the whole `HasDirichletDensity`/`limsup`/`liminf` API right below uses `𝓝[>] (1:ℝ)`. A complex variable would be a *different* object (the analytic continuation), not a weakening. |
| 4 | output `ℝ`                               | real-valued partial sum                    | real-valued (for density)              | no                  | matches the literature density numerator. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** *within the number-field / mathlib substrate it sits on.*
Number of weakening opportunities found: 1 nominal (number field → global field), but it is **not
actionable**: mathlib has no global-field zeta/density infrastructure to generalise onto, and the
project's whole density API (`HasDirichletDensity`, the `log (s-1)⁻¹` asymptotic via `dedekindZeta`,
the cyclotomic/abelian Chebotarev machinery) is number-field-specific. Per the skill's cost rule,
EXPENSIVE-with-no-substrate is a *sequencing* note, not a verdict downgrade — and here it isn't even
the gating issue, because mathlib doesn't have the object at all (see Phase 5).

Cost of the global-field restatement: **EXPENSIVE** (needs an entire global-field-uniform zeta/Euler-
product layer that mathlib lacks). Not pursued.

### 4c. Modern-idiom check (Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let X be a foo" preambles → typeclasses? | no | `[NumberField K]` is already a typeclass; the set `S` is genuinely data | — |
| 2  | sequences/metric → filters/topological? | no | already filter-based downstream (`𝓝[>] 1`, `limsup`/`liminf`); the *def* itself is a plain `tsum` (the right primitive) | — |
| 3  | construct object → universal-property class? | no | a Dirichlet series is a concrete sum, not a universal-property object | — |
| 4  | set-with-predicate → bundled substructure? | partial | the index `{𝔭 // 𝔭∈S ∧ IsPrime ∧ ≠⊥}` could be phrased via `S ∩ {primes}`; but the subtype `tsum` is the idiomatic mathlib spelling (cf. how mathlib writes `∑' i : {x // p x}`) | none material |
| 5  | vector/metric/field-specific → weaken typeclass? | no | output is `ℝ` (the density target); no algebraic over-strength | — |
| 6  | 1-categorical → higher-categorical? | no | N/A | — |
| 7  | concrete index ℕ/ℤ/ℝ → general monoid/group? | partial | the *exponent* `s : ℝ` could be `ℂ` — but that yields a **different** object (the analytic partial zeta), and density needs real `s` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The definition is already in the idiomatic mathlib shape — a `tsum`
over a subtype with a real exponent, designed to plug into the filter-based `𝓝[>] 1` density API
immediately below it. The one nominal modernisation (complex exponent) is not a modernisation but a
*change of object* (analytic zeta ≠ density numerator). No genuine organisational improvement is on
the table.

---

## PHASE 4.5 — Diamond / defeq risk (`def`)

### 4.5a. Risk table

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none | introduces no instance; it is a plain `noncomputable def : ℝ`. No `[…]` output, nothing for `synthInstance` to pick. |
| 2 | Reducibility leak            | low  | not `@[reducible]`; the equation lemma `primeIdealZetaSum_def` (`:= rfl`) is provided precisely so consumers rewrite explicitly rather than relying on `simp` unfolding the `tsum`. Sealed barrier is intentional and correct. |
| 3 | Non-canonical unfolding      | low  | `simp`/`rfl` will not spontaneously unfold it (no `@[simp]`); unfolding is via the explicit `primeIdealZetaSum_def`. As used in the file (15+ `rw [primeIdealZetaSum_def]` sites) this is well-behaved. |
| 4 | Instance priority collision  | n/a  | not an `instance`. |
| 5 | Universe-polymorphism issues | none | all types are concrete (`Ideal (𝓞 K) : Type`, output `ℝ`); `K : Type*` is the only universe var and it is unconstrained-as-usual. |
| 6 | Coercion ambiguity           | none | no `CoeFun`/`CoeSort`; the only coercions are the standard `ℕ → ℝ` on `absNorm` and `ℝ`-`rpow`, both canonical. |

### 4.5b. Risk verdict

Overall risk: **LOW.** Top risks: none HIGH. A plain real-valued `tsum` def with a companion `rfl`
equation lemma — exactly the safe pattern. No mitigations required.

---

## PHASE 5 — Mathlib search

### Five-method search-status: `Chebotarev.primeIdealZetaSum`

- **[A] Lean-Finder** — n/a: MCP index unavailable in this thread.
- **[B] Loogle** — `Ideal.absNorm _ ^ _` (via loogle web `json` endpoint): **no hits** that are
  `tsum`/`HasSum`/`Summable` over (prime) ideals; only `absNorm_eq_pow_inertiaDeg…` and
  `absNorm_algebraMap`. No zeta-sum-over-ideals, no Dirichlet density. ⇒ no hit.
- **[C] LeanSearch** — n/a: MCP index unavailable; substituted by direct grep + Loogle.
- **[D] Grep mathlib src** (`.lake/packages/mathlib`, authoritative, pinned version):
  - `dirichlet.?density|HasDirichletDensity|primeZeta|prime.?ideal.?zeta` over all of `Mathlib/` → **no hits**.
  - `density` in `Mathlib/NumberTheory/` → only `Transcendental/Liouville/Residual.lean` (unrelated topological density).
  - `tsum|HasSum|Summable` ∧ `absNorm|Ideal` in `Mathlib/NumberTheory/NumberField/` → **no hits** (no zeta sum over ideals at all).
  - `Set (Ideal` in `Mathlib/NumberTheory/` → **no hits** (mathlib never indexes a zeta-type sum by a set of ideals).
  - `dedekindZeta` (`Mathlib/NumberTheory/NumberField/DedekindZeta.lean`) → defined as
    `LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s` — indexed by the **integer norm
    value `n : ℕ`** over **all** integral ideals, **complex** `s`. **Not** prime-restricted, **not**
    set-restricted, **not** real-`s`. A structurally different object.
- **[E] Name pattern** — n/a: `lean_local_search` would not resolve project decls on a stale build;
  grep substituted (above).

Searched for both: the user's current form (prime-set real-`s` sum) **and** the literature-standard
form (density numerator / partial Dedekind zeta). Neither is in mathlib.

Concluded: **not in mathlib** (grep + Loogle exhausted, plus the literature-standard form). The nearest
mathlib object, `NumberField.dedekindZeta`, is the *full* zeta indexed by integer norm value over all
ideals with complex `s` — neither it nor any of its lemmas expresses a prime-restricted, set-indexed,
real-variable partial sum.

---

## PHASE 6 — Composition check

### 6.0. Call sites — `Chebotarev.primeIdealZetaSum`

Internal use count: **very high** — used pervasively in the declaring file `Density.lean` (≈40
occurrences: `_def`, `_nonneg`, `_le_univ`, `_le_of_subset`, `_union_of_disjoint`,
`_biUnion_of_pairwiseDisjoint`, `_eq_univ_of_forall_prime_mem`, `_univ_eq_tsum_prime2`,
`_univ_tendsto_log`, `logDedekindZeta_sub_primeIdealZetaSum_bounded`, the three density `def`s, …).

External-to-file callers: **5 distinct files** in the project.

| Caller file:line                                   | Usage pattern (one-line excerpt) |
|----------------------------------------------------|-----------------------------------|
| `CebotarevDensity/Abelian.lean:859,880,1313,…` (25 lines) | `primeIdealZetaSum Sσ s / primeIdealZetaSum (Set.univ …) s` (density ratios in the abelian Chebotarev sandwich) |
| `CebotarevDensity/CyclotomicNormResidue.lean` (31 lines) | builds the cyclotomic norm-residue density on `primeIdealZetaSum` |
| `CebotarevDensity/FixedFieldDensity.lean` (41 lines)     | fixed-field density manipulations of the ratio |
| `CebotarevDensity/Cyclotomic.lean` (41 lines)           | cyclotomic-field density |
| `CebotarevDensity/Main.lean` (10 lines)                  | top-level density statements |

Inline-derivation grep (was the equivalent re-derived without `primeIdealZetaSum`?): **none** — every
consumer goes through the named def; there is no bypassing inline `∑' 𝔭 …` re-derivation.

**Signal:** ≥3 internal uses, 5 external caller files, zero inline re-derivation ⇒ this is a *real,
load-bearing API object*, the foundation of the project's density layer. Strong YES-bucket signal.

### 6a. Composition check

Can `Chebotarev.primeIdealZetaSum` be obtained from mathlib in ≤3 chained calls? **No.** The object is
a `def` of a *new sum*, not a derivable statement. Mathlib offers the generic primitive `tsum` and the
generic `Ideal.absNorm` and `Real.rpow`, but assembling them into "the sum of `absNorm 𝔭 ^ (-s)` over
`{𝔭 ∈ S | prime, ≠⊥}`" **is exactly authoring this definition** — there is no mathlib lemma/def whose
composition *yields* it. (Contrast: a glue lemma like `_def := rfl` is composable; the underlying named
object is not "composed", it is *defined*.) Mathlib's `dedekindZeta` cannot be specialised to it (wrong
index — integer norm value, not a set of primes; wrong variable — complex, not real).

Conclusion: **NOT-COMPOSABLE.**

---

## Verdict: `Chebotarev.primeIdealZetaSum`

**Category:** **YES-but-generalise-first** *(borderline against YES-add-as-is — see rationale)*

**Evidence:**
- Literature search (Phase 3): the density numerator $\sum_{\mathfrak p\in S}N\mathfrak p^{-s}$ is a
  standard, universally-used object (Wikipedia, Stevenhagen–Lenstra, Conrad, current arXiv); it has
  **no standalone textbook name** and the literature states it for **global fields** with **real** `s`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the number-field substrate; one nominal
  weakening (number field → global field), EXPENSIVE and with no mathlib substrate. Modern-idiom: none.
- Diamond/defeq risk (Phase 4.5): LOW (plain real `tsum` def + `rfl` equation lemma).
- Mathlib search (Phase 5): **not in mathlib**; nearest object `NumberField.dedekindZeta` is the full
  integer-norm-indexed complex zeta over all ideals — structurally different.
- Composition check (Phase 6): NOT-COMPOSABLE; 5 external caller files, ≈40 internal uses, no inline
  re-derivation — a genuine load-bearing API object.

**Rationale (why YES-but-generalise-first rather than YES-add-as-is):**

This is real mathematical content that mathlib is missing: mathlib has the *full* Dedekind zeta
(`NumberField.dedekindZeta`, indexed by integer norm value, complex variable, all ideals) but **no**
prime-restricted, set-indexed partial sum, and **no** Dirichlet-density notion built on it — the
`density` grep over all of `Mathlib/` returns nothing in number theory. The named gap is concrete:
mathlib's number-field analytic layer stops at the class-number formula
(`tendsto_sub_one_mul_dedekindZeta_nhdsGT`) and never introduces the density machinery
(`HasDirichletDensity` and friends) that Chebotarev/Dirichlet-density arguments require. So the object
is wanted.

It lands in **YES-but-generalise-first** rather than YES-add-as-is for a *formulation* reason, not a
cost dodge. The way it is currently sealed to a **number field** + a **`Set (Ideal (𝓞 K))`** + a
**real** exponent makes it a specialisation of the literature-standard **global-field** density
numerator $\sum_{v\in S}q_v^{-s}$. Before mathlib adopts a *Dirichlet density* definition it is worth
deciding the right home object — most plausibly defining the partial sum / density against a
global-field (or at least a re-usable "primes with residue-norm") interface, or at minimum factoring
out a reusable `primePartialZeta`/density-numerator that mathlib's eventual Chebotarev development would
share, rather than baking it inside one project's `Chebotarev` namespace. That said, because mathlib
currently has **no** global-field zeta substrate at all, the honest generalisation target may be "ship
the number-field form now, designed so the density API around it is the canonical one" — which is why
this is flagged for a human/`/generalise` judgement rather than auto-actioned.

**Reason for the generalisation:** LITERATURE-WEAKENING (Phase 4b: the number-field/real-`s`/`Set
(Ideal)` form is a specialisation of the global-field density numerator) — *modulo* the substrate
caveat that mathlib lacks the general layer, which is itself the thing to resolve before upstreaming.

**Proposed restatement (target to tension against in `/generalise`):**
```lean
-- Option A (minimal, number-field, but factored as the canonical density-numerator API):
/-- The prime-ideal partial zeta sum `∑_{𝔭 ∈ S} N𝔭^{-s}`, the numerator of the Dirichlet density. -/
noncomputable def primePartialZeta {K : Type*} [Field K] [NumberField K]
    (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
-- Option B (the literature-general target, BLOCKED on missing mathlib infrastructure):
--   a global-field / "primes with finite residue field" indexed numerator ∑_{v ∈ S} q_v^{-s};
--   not currently expressible — mathlib has no uniform global-field residue-norm zeta layer.
```

**Estimated cost of regeneralisation:** Option A = CHEAP (rename + relocate); Option B = EXPENSIVE and
currently BLOCKED (no mathlib substrate). Cost does not downgrade the verdict.

**Mathlib downstream this enables:** a canonical Dirichlet-density layer (`HasDirichletDensity`,
upper/lower variants) that the eventual mathlib Chebotarev density theorem and Dirichlet's theorem on
primes-in-progressions-for-number-fields would both consume; the `log (s-1)⁻¹` asymptotic of the
denominator already proved here (`primeIdealZetaSum_univ_tendsto_log`) becomes reusable.

**Next action:** run `/generalise Chebotarev.primeIdealZetaSum` to tension the current form against the
global-field literature target and the "factor out the canonical density-numerator" modern target; a
human should decide whether mathlib wants the number-field form now (Option A) or waits for a
global-field zeta layer (Option B). Given the BIG/foundational status and the global-field gap, this is
deliberately not auto-actioned.

---

## Next step

Run `/generalise Chebotarev.primeIdealZetaSum`, then take the formulation decision (Option A now vs.
Option B blocked-on-substrate) to a human before any mathlib PR.
