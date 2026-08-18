# /mathlibable report — `Chebotarev.chebotarev_abelian`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. Environment notes (per the task + the sibling
> `chebotarev_density.md` / `dirichlet_primes_in_AP.md` runs): the ChatGPT-math MCP
> is down and the Loogle / LeanSearch / Lean-Finder MCPs are not loadable in this
> env, so the literature channel uses the documented WebSearch + WebFetch +
> nLab/EoM fallback, and Phase 5 ("is it in mathlib") is answered by **direct grep
> over the vendored mathlib tree** `.lake/packages/mathlib/Mathlib/` plus reading
> mathlib source docstrings, both of which are authoritative. The local Lean build
> is stale (Phase 0a reasoned from source, not rebuilt).

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:               (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.chebotarev_abelian`:  ✓ resolved at
                            projects/Chebotarev/CebotarevDensity/Abelian.lean:1578
- true qualified name:      Chebotarev.chebotarev_abelian
                            (namespace `Chebotarev` opened Abelian.lean:56;
                            `end Chebotarev` Abelian.lean:1595; theorem at 1578 ⇒
                            the parsed guess `Chebotarev.chebotarev_abelian` is CORRECT)
- kind:                     theorem
- has sorry:                no (proof complete: routes the three ingredients
                            `liminf_ratio_ge_inv_card_G`,
                            `ratioSum_frobeniusFibres_tendsto_one`,
                            `isBoundedUnder_ge_ratio_zetaSum` through the pigeonhole
                            glue `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`)
- module docstring summary: Chebotarev's density theorem (abelian case) — the
                            density of primes 𝔭 of 𝓞 K unramified in L with a given
                            Frobenius is 1/|Gal(L/K)|; Sharifi 7.2.2 Step 2.
```

The variables `K L : Type*` and the field/number-field/Galois typeclasses are bound
at Abelian.lean:58 (one `variable` line for the whole `Chebotarev` namespace).

---

## Phase 1 — Statement (prose)

`Chebotarev.chebotarev_abelian` is **Chebotarev's density theorem in the abelian
case** — the per-element density statement for an abelian (commutative) Galois group:

> Let `L/K` be a finite **abelian** Galois extension of number fields, with
> `G = Gal(L/K)` (so every conjugacy class is a singleton and the Frobenius of an
> unramified prime is a well-defined *element* of `G`). Fix `σ ∈ G`. Then the set
> of primes `𝔭` of `𝓞 K`, unramified in `L`, whose Frobenius equals `σ`, has
> **Dirichlet density** `1/|G|`.

This is the analytic heart of the Chebotarev story: it is the case the *general*
(conjugacy-class) Chebotarev theorem reduces to — pass from a class `C = {σ}` of `G`
to the cyclic subgroup `⟨σ⟩` and its fixed field `E = L^⟨σ⟩`, over which `L/E` is
abelian (indeed cyclic), apply this theorem, then push the density back down to `K`
by a counting argument. In the project this reduction is exactly
`density_lift_through_fixedField` + `chebotarev_abelian` (`Main.lean:84–87`). The
abelian case in turn reduces (inside this file's machinery) to the cyclotomic case
via the admissible-prime crossing argument (`exists_admissible_prime`,
`liminf_density_S_sigma_ge_card_H_n_div_GH`).

**Variables / typeclasses (Lean side):**
- `{K L : Type*}` with `[Field K] [NumberField K] [Field L] [NumberField L]` — two
  number fields (bound at Abelian.lean:58).
- `[Algebra K L] [IsGalois K L]` — `L/K` is a (finite) Galois extension. (Finiteness
  is automatic from `NumberField` + `IsGalois`; `Gal(L/K)` is finite.)
- `[hAb : IsMulCommutative Gal(L/K)]` — the Galois group is **abelian**. This is the
  case-specific hypothesis, written with mathlib's own modern `IsMulCommutative`
  typeclass (the commutativity-as-a-`Prop`-mixin idiom).
- `(σ : Gal(L/K))` — the target Galois element (= the singleton Frobenius class).

**Hypotheses (Lean side):** all carried by typeclasses above; the only explicit term
argument is `σ`.

**Conclusion (math):** the Frobenius-fibre over `σ` has Dirichlet density `1/|G|`.

**Conclusion (Lean):**
```lean
HasDirichletDensity
  {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
    frobeniusClass K L 𝔭 = ConjClasses.mk σ}
  ((Nat.card Gal(L/K) : ℝ)⁻¹)
```
where the three ingredients are **project** definitions:
- `HasDirichletDensity S δ` (`Density.lean:64`, Sharifi 7.1.13) :=
  `Tendsto (fun s ↦ (Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})) (𝓝[>] 1) (𝓝 δ)` — the
  analytic (Dirichlet) density via the ratio of partial Dirichlet sums as `s ↓ 1⁺`.
- `frobeniusClass K L 𝔭` (`Frobenius.lean:188`) := the conjugacy class of the
  arithmetic Frobenius `arithFrobAt` for any maximal `𝔓 ∣ 𝔭` (well-defined for
  unramified nonzero `𝔭`); here, `G` being abelian, `ConjClasses.mk σ = {σ}`.
- `UnramifiedIn K L 𝔭` (`Frobenius.lean:62`) := `𝔭 ≠ ⊥` and every maximal prime
  above it is unramified.

Note the conclusion is phrased with `frobeniusClass … = ConjClasses.mk σ` (a class
equality) even though `G` is abelian — i.e. it shares the *exact* set-shape of the
general `chebotarev_density`, so it is the literal `IsMulCommutative` specialisation,
not a re-packaging.

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: BIG.** Two independent triggers fire:
1. It is the **abelian case of a theorem named after a person** (Chebotarev /
   Cebotarev) — a recognised, named landmark whose abelian/cyclic case is itself a
   named, separately-cited stage of the standard proof (the case the general theorem
   reduces to). Essentially guaranteed to be in the literature.
2. It is a **declared main result** of the project — first bullet of the
   `## Main results` block of the `Abelian.lean` module docstring (Abelian.lean:38),
   and the analytic kernel that `Main.lean`'s `chebotarev_density` /
   `chebotarev_density_of_comm` are built on.

(Literature width is EXHAUSTIVE regardless. Recorded for framing: this is the
load-bearing analytic core, not a throwaway helper.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`. (Body is a ~10-line proof: `simp only` to
unfold `HasDirichletDensity` + `Nat.card_eq_fintype_card`, then a single
`refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one …` feeding the three
ingredient lemmas into the pigeonhole glue, then `simpa … using liminf_ratio_ge_inv_card_G`.)

---

## Phase 3 — Literature search (EXHAUSTIVE)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Chebotarev density theorem abelian case cyclic Galois extension Dirichlet density 1/\|G\| proof reduction" | **yes** | for an abelian `L/F_σ`, `d(T_σ) = 1/#H_σ`; the general theorem is *derived from* this abelian/cyclic case via the cyclic subgroup `⟨σ⟩` and fixed field `F_σ = L^{⟨σ⟩}` | MIT 18.785 L28, Lenstra (Leiden), Triantafillou notes, Di Meglio, Lagarias–Odlyzko — **verbatim the proof route the project takes** (Sharifi 7.2.2 Step 2) |
| 2 | WebSearch (general / reduction axis) | "Chebotarev density theorem proof abelian case first reduce to cyclotomic fields then general case fixed field" | **yes** | the **abelian case is reduced to the cyclotomic case** by Chebotarev's field-"crossing" argument; the general case is reduced to the abelian case by class field theory / the fixed-field counting (Deuring) | Di Meglio, Stevenhagen–Lenstra `cheb.pdf`, MIT 18.785 L28 — confirms the **two-stage** structure (general ⇐ abelian ⇐ cyclotomic), exactly the project's `Main` ⇐ `Abelian` ⇐ `Cyclotomic` layering |
| 3 | WebSearch (named-after / Lean-mathlib status) | "mathlib4 Lean Chebotarev density theorem formalization status FLT project 2025 abelian case not yet" | **partial** | — | Chebotarev (incl. its cases) is a **needed dependency of FLT** and a **stretch goal of PNT+** ("A version of it is needed for the proof of FLT"; "long-term objective"). Confirmed *ongoing, not landed*. No mention of the abelian case being separately in mathlib. |
| 4 | ChatGPT MCP | self-contained 3-part standard-form / generality / mathlib-status query | **n/a — MCP down** | — | fell back to WebSearch + WebFetch + nLab/EoM per the skill's documented fallback |
| 5 | Local references | grep `.mathlib-quality/references/` (and `refs/Chebotarev/`) | **n/a — absent** | — | no `references/` dir in the project; `refs/` shared store not present in this checkout (PDFs are local-only: Sharifi `algnum.pdf` §7.2.2, SL `cheb.pdf`) |
| 6 | nLab | "Chebotarev density theorem" page | **n/a — 404** | — | nLab has no dedicated Chebotarev page; the concept lives under class field theory / Frobenius. Not a categorical concept. |
| 7 | nCatLab | (categorical?) | **n/a** | — | not a categorical concept; the abelian case is an analytic-NT density statement |
| 8 | Stacks Project | "Chebotarev density / Frobenius element density" | **n/a** | — | Stacks has no Chebotarev / analytic-density-of-primes material; out of scope |
| 9 | Encyclopedia of Mathematics / MathOverflow | "Chebotarev density abelian case = class field theory / Dirichlet density of Frobenius element" | **yes** | the abelian case of Chebotarev *is* (equivalent to) the density statement of class field theory; for `σ ∈ G` abelian, the primes with Frobenius `σ` have Dirichlet density `1/\|G\|` | EoM "Density theorem" / "Chebotarev density theorem"; MO threads on "Chebotarev abelian case = CFT" — confirms the value `1/\|G\|` and that the abelian case is a recognised, named statement |
| 10 | recent arXiv (last 5y) | "effective / unified Chebotarev density theorem abelian cyclic case" | **yes** | the strictly-stronger axes: **effective/quantitative** Chebotarev (error terms, GRH-conditional), and **natural density / asymptotic count** `N_σ(x) ∼ x/(|G| log x)` | e.g. arXiv 1803.02823 "A unified and improved Chebotarev density theorem"; Lagarias–Odlyzko "Effective versions" — strengthenings, not weakenings, of the abelian Dirichlet-density statement |

### Literature summary (Phase 3)

**Concept identified as:** the **abelian (= cyclic-reducible) case of the Chebotarev
density theorem** — equivalently, the density statement underlying class field
theory: for `σ` in an abelian `G = Gal(L/K)`, the primes with Frobenius `σ` have
Dirichlet density `1/|G|`.

**Sources agree on the standard form: yes.** MIT 18.785 (Lecture 28), Lenstra's
Chebotarev notes, Stevenhagen–Lenstra `cheb.pdf`, Triantafillou, Di Meglio, and the
Encyclopedia of Mathematics all present the abelian case with density value `1/|G|`
(equivalently `1/#H_σ` over the fixed field), and all use it as **the** intermediate
stage: *general ⇐ abelian ⇐ cyclotomic*. This matches the Lean form verbatim
(`HasDirichletDensity … (|G|)⁻¹`, `G` abelian via `IsMulCommutative`).

**Most general standard form:** the *value* `1/|G|` and the abelian hypothesis are
fixed across the literature; the generality axes are the **base field** (number field
⊊ global field), the **density notion** (Dirichlet ⊊ natural ⊊ effective), and
whether one states it per-element `σ` or per-subset — not the abelian hypothesis or
the value. The number-field / Dirichlet-density / per-element form is the canonical
textbook statement and the one the general Chebotarev (and FLT) consumes.

**Generality dimensions where the literature varies:**
- *Base field*: number field ⊊ global field (function-field abelian case is a
  genuinely different proof — Frobenius on a curve, no `s→1⁺` Dedekind-zeta density).
- *Density notion*: Dirichlet density (weakest, cleanest, no error term) ⊊ natural
  density ⊊ effective/quantitative (Lagarias–Odlyzko; GRH-conditional bounds).
- *Per-element vs per-subset*: the per-element `σ` statement and the
  "density `|A|/|G|` for a subgroup-/subset-`A`" statement are trivially
  interchangeable in the abelian case (sum over elements).

**Disagreement with the literature: none.** The Lean form is the literature-standard
abelian case at its canonical generality (number field, Dirichlet density,
per-element `σ`, value `1/|G|`).

---

## Phase 4 — Generality analysis

**Literature-standard form (from Phase 3):** for a finite **abelian** Galois
extension of **number fields** and `σ ∈ G`, the primes with Frobenius `σ` have
**Dirichlet density** `1/|G|`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K] [NumberField L]` | number fields | global fields (number + function) | yes (global fields) | **NO for this proof.** The function-field abelian case is a genuinely different theorem with a different proof (no `s→1⁺` Dirichlet density via `DedekindZeta`). Number-field case is the canonical statement and the FLT-needed one. Generalising = a separate development, not a weakening of *this* proof. |
| 2 | `[IsMulCommutative Gal(L/K)]` | `G` abelian | `G` abelian (the defining hypothesis of the *case*) | **no — removing it gives a different theorem** | This is precisely the case hypothesis. Dropping it is not a *weakening*; it is the **general** Chebotarev (`chebotarev_density`, already in the project), whose proof is strictly more (it *reduces to* this abelian case). So this row is the case boundary, not a missed generalisation. |
| 3 | `[IsGalois K L]` (+ finiteness from `NumberField`) | finite Galois | finite Galois | **no** | exactly the standard hypotheses; `G` must be finite for `1/\|G\|` to make sense. |
| 4 | density notion (`HasDirichletDensity`) | Dirichlet density | Dirichlet (weak) or natural (strong) | the *natural-density* form is strictly **stronger**, not weaker | Natural/effective density ⇒ Dirichlet density (not conversely); needs PNT-/GRH-grade analytic input mathlib lacks. A **strengthening**, not a weakening. |
| 5 | conclusion shape (`frobeniusClass … = ConjClasses.mk σ`, value `(\|G\|)⁻¹`) | per-element `σ`, density `1/\|G\|` | per-element `σ` **or** per-subset, density `\|A\|/\|G\|` | the per-subset form is an equivalent **reformulation**, not a weakening | In the abelian case `ConjClasses.mk σ = {σ}`, so this *is* the `\|C\|=1` instance of the general conjugacy-class form. The per-subset version is a one-line corollary (sum over `σ ∈ A`), not a reason to restate. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** for the number-field / Dirichlet-density
**abelian case** — it is exactly the standard textbook statement of that case.

Number of genuine *weakening* opportunities found: **0**. The "more general" axes
are all either (a) a **different/stronger theorem** — dropping abelian gives the
general Chebotarev (already present as `chebotarev_density`), and natural/effective
density needs machinery mathlib lacks — or (b) an **equivalent reformulation**
(per-subset), which is a thin corollary. None is an assumption-weakening of *this*
proof.

Cost of "generalising" past abelian (to general Chebotarev) or to natural density:
**EXPENSIVE — needs new ideas / is a separate result.** Per the skill's cost rule
this does **not** downgrade the verdict and does **not** make it
YES-but-generalise — these are follow-on / sibling theorems, not a better statement
of *this* result. (Indeed the general theorem is the *consumer* of this one, the
wrong direction for "generalise first".)

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Downstream this enables |
|---|----------|----------|------------------------|-------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | **already done** | `NumberField`, `IsGalois`, and crucially the abelian hypothesis `IsMulCommutative Gal(L/K)` are all typeclasses; `σ` is a first-class group element | already maximally idiomatic; `IsMulCommutative` is mathlib's own commutativity mixin (Algebra/Group/Defs.lean:206), the contemporary spelling of "abelian" |
| 2 | sequences/metric → filters/topology? | **already done** | density is `Tendsto … (𝓝[>] 1) (𝓝 δ)` (filter form), not an ε-sequence | composes with all of mathlib's filter-limit API |
| 3 | construct an object → universal-property class? | no | — | the statement is a `Prop` asserting a density value; nothing to characterise universally |
| 4 | set-with-closure → bundled substructure? | no | — | `Ideal` / `ConjClasses` are already the right bundled types; the fibre is a `Set (Ideal …)` with a predicate, the correct shape |
| 5 | vector-space/field-specific → weaken typeclasses? | no | — | already at `NumberField`, the correct generality for the analytic (`DedekindZeta`-based) proof |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorical statement |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary structure? | partial | the per-element `σ` form could be stated for a subset `A ⊆ G` (density `\|A\|/\|G\|`) | corollary only; see 4a row 5 — a thin sum-over-elements, not a restatement |

**Modern-idiom verdict: no further modernisation move available.** The statement
already uses the contemporary mathlib idioms — `IsMulCommutative` (the modern
"abelian" mixin) rather than a bundled `CommGroup` preamble, filter-based `Tendsto`
density, `ConjClasses` / `arithFrobAt`, `Gal(L/K)` notation. The only "more general"
reformulations (per-subset; dropping abelian) are either a thin corollary or the
*separate* general theorem. One genuine API-surface note for the eventual PR (shared
with the `chebotarev_density` assessment): mathlib will want the supporting **defs**
`HasDirichletDensity`, `frobeniusClass`, `UnramifiedIn` promoted to canonical
definitions first — see Phase 7.

---

## Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (no definitional equalities / typeclass-search
paths introduced). Skipped.

> Carried to Phase 7 (shared with the `chebotarev_density` / `dirichlet_primes_in_AP`
> assessments): the *supporting definitions* `HasDirichletDensity` (`Density.lean:64`),
> `frobeniusClass` (`Frobenius.lean:188`), `UnramifiedIn` (`Frobenius.lean:62`) are
> `def`s and each warrant their own Phase-4.5 pass when **they** are upstreamed. They
> are out of scope for this single-declaration (theorem) assessment but are the real
> definitional prerequisites this theorem travels with.

---

## Phase 5 — Mathlib search (five-method)

```
### Mathlib search-status: Chebotarev.chebotarev_abelian

[A] Lean-Finder       (MCP unavailable in this env)   n/a — tool not loadable; substituted grep [D]
[B] Loogle            (MCP unavailable in this env)    n/a — tool not loadable; substituted grep [D]
[C] LeanSearch        (MCP unavailable in this env)    n/a — tool not loadable; substituted grep [D] + mathlib docstring reads
[D] Grep mathlib src  "chebotarev|cebotarev|čebotarev"                                  NO HITS in .lake/packages/mathlib/Mathlib/
                      "DirichletDensity|dirichletDensity|analyticDensity|naturalDensity"  NO HITS
                      "density.*prime|prime.*density|equidistribut" (in NumberTheory/)    NO HITS (no analytic prime-density infra)
                      "frobeniusClass|frobenius_class"                                    NO HITS
                      "arithFrobAt|IsArithFrobAt"                                          HIT: RingTheory/Frobenius.lean (building block only)
                      "IsMulCommutative" (the abelian hypothesis spelling)                HIT: Algebra/Group/Defs.lean:206 (mathlib's own class — confirms modern idiom)
                      "dedekindZeta|DedekindZeta|zetaSum"                                  HIT: NumberTheory/NumberField/DedekindZeta.lean (building block only)
                      "infinite_setOf_prime_and_eq_mod" + PrimesInAP docstring            HIT: NumberTheory/LSeries/PrimesInAP.lean — INFINITUDE only ("two versions", both infinitude)
[E] Name pattern      (lean_local_search unavailable; grep over project + mathlib used)   as above
```

**Searched for both forms:**
- *User's form* (abelian-case Chebotarev, Dirichlet density `1/|G|` of primes with
  Frobenius `σ`): **not in mathlib.**
- *Literature-standard / stronger / more-general forms* (general-Galois Chebotarev;
  natural-density asymptotic count; effective Chebotarev; any "Dirichlet/analytic
  density of a set of prime ideals" at all): **not in mathlib.** The closest
  analytic-NT result, `Nat.infinite_setOf_prime_and_eq_mod`
  (`NumberTheory/LSeries/PrimesInAP.lean:475`), is the **infinitude** form of the
  `K=ℚ`/cyclotomic special case — its own docstring (lines 60–64) says it gives
  "two versions of **Dirichlet's Theorem**", and **both** are infinitude (the set is
  `Infinite` / `∃ p > n`). There is **no density layer** anywhere in mathlib.

**Concluded:** **not in mathlib** (all available methods exhausted, plus the
literature-standard, more-general, and stronger forms). Mathlib has only the
**building blocks** — `arithFrobAt` (`RingTheory/Frobenius.lean`),
`DedekindZeta` (`NumberTheory/NumberField/DedekindZeta.lean`), `IsMulCommutative`
(`Algebra/Group/Defs.lean`), `ConjClasses`/`Nat.card` — and the *infinitude* version
of the `ℚ`/cyclotomic special case. Never the abelian-case density statement, never
any Chebotarev, never any analytic density of prime ideals. The two flagship
in-progress efforts (FLT, PNT+) list Chebotarev as a wanted-but-unfinished
dependency / stretch goal.

---

## Phase 6 — Composition check (+ call-sites)

### 6.0. Call sites — `Chebotarev.chebotarev_abelian`

Internal use count: **2** (within the project, excluding the declaring file).
External-to-file callers: 1 distinct file (`Main.lean`), 2 call sites — both genuine
*consumers*, not re-derivations.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `CebotarevDensity/Main.lean:87` | `… (chebotarev_abelian _ L (e ⟨σ, Subgroup.mem_zpowers σ⟩))` — fed into `density_lift_through_fixedField` to prove the **general** `chebotarev_density` by reducing to the cyclic fixed field `E = L^⟨σ⟩` |
| `CebotarevDensity/Main.lean:110` | `simpa [ConjClasses_carrier_card_eq_one_of_comm σ] using chebotarev_abelian K L σ` — proves `chebotarev_density_of_comm` (the bundled abelian-case restatement with `\|C\|/\|G\|` value) directly |

(The other `chebotarev_abelian` occurrences in the repo — Abelian.lean:38/61/553/554/1500,
Main.lean:25, FixedFieldDensity.lean:23/1121 — are all **docstring / comment**
mentions, not calls. FixedFieldDensity.lean:23 explicitly notes its block is
"`chebotarev_abelian`-independent".)

Inline-derivation grep (was the `1/|G|`-density abelian statement re-derived
elsewhere without this lemma?): **none.** No file re-proves the abelian-case density
by hand; the general theorem and its commutative restatement both route through this
theorem.

**Reading per the Phase-6 call-site table:** `K = 2` internal uses, no inline
re-derivation → this is the **"real API root"** pattern (K ≥ 1 proper consumers, no
bypass). It is the analytic kernel the general Chebotarev (`chebotarev_density`,
Main.lean:71) and its abelian restatement (`chebotarev_density_of_comm`, Main.lean:103)
are built on. Strong YES-leaning composability signal.

### 6a. Composition attempt

Can `chebotarev_abelian` be derived from **mathlib** in ≤3 chained calls?

- **Attempt 1 — from any mathlib density/equidistribution lemma:** **fails at step 0.**
  Mathlib has **no** notion of Dirichlet/analytic density of a set of primes at all
  (Phase 5), hence no Chebotarev, no abelian case, no Frobenius-equidistribution
  lemma to chain from. There is nothing to compose.
- **Attempt 2 — from mathlib's `Nat.infinite_setOf_prime_and_eq_mod`:** **fails.**
  That gives only *infinitude* of primes in the `ℚ`/cyclotomic AP special case;
  infinitude does not imply a density value, and it is not even the general-field
  abelian statement. No mathlib lemma turns it into "Dirichlet density `1/|G|`".
- **Attempt 3 — assemble from `DedekindZeta` + `arithFrobAt` + `ConjClasses`:**
  **fails.** This is not a 1–3-call composition; it is the entire proof. The project
  proof itself is a multi-ingredient assembly — a per-fibre `liminf ≥ 1/|G|` bound
  (`liminf_ratio_ge_inv_card_G`, itself the limit over admissible cyclotomic primes
  of `liminf_density_S_sigma_ge_card_H_n_div_GH`), a sum-to-one statement
  (`ratioSum_frobeniusFibres_tendsto_one`), and a real-analysis pigeonhole glue
  (`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`) — sitting atop a 1500-line file
  and the `Cyclotomic`/`FixedFieldDensity` machinery. The bricks exist; the *theorem*
  is hundreds of lines of new mathematics.

**Conclusion: NOT-COMPOSABLE.** The canonical "mathlib has the bricks, not the
building" case — and the building is large.

---

## Phase 7 — Verdict

## Verdict: `Chebotarev.chebotarev_abelian`

**Category:** YES-add-as-is

**Evidence:**
- **Literature search (Phase 3):** the abelian/cyclic case of Chebotarev with
  Dirichlet density `1/|G|` is *the* standard intermediate stage of the theorem,
  agreed across MIT 18.785 L28, Lenstra, Stevenhagen–Lenstra, Triantafillou, Di
  Meglio, and EoM (where the abelian case = the density content of class field
  theory). The Lean form matches verbatim, with `G` abelian via mathlib's own
  `IsMulCommutative` and value `(|G|)⁻¹`.
- **Generality analysis (Phase 4):** MAXIMALLY GENERAL for the number-field /
  Dirichlet-density abelian case; the only "more general" axes (dropping abelian →
  the general Chebotarev, which is a *separate, stronger* theorem already present;
  global fields; natural/effective density) are different/stronger results, not
  weakenings (cost EXPENSIVE, non-downgrading per the rules). Modern-idiom: already
  idiomatic (`IsMulCommutative`, filter `Tendsto` density, `ConjClasses`,
  `arithFrobAt`).
- **Mathlib search (Phase 5):** not in mathlib by any method; only building blocks
  present (`arithFrobAt`, `DedekindZeta`, `IsMulCommutative`, `ConjClasses`); the
  nearest neighbour `Nat.infinite_setOf_prime_and_eq_mod` is infinitude-only of the
  `ℚ` special case. The two flagship projects (FLT, PNT+) want Chebotarev and have
  not landed it.
- **Composition check (Phase 6):** NOT-COMPOSABLE — it is a large multi-file proof,
  not a ≤3-call composition; and it is a genuine API root with 2 internal consumers
  (`chebotarev_density`, `chebotarev_density_of_comm`) and no inline re-derivation.

**Rationale.**
`chebotarev_abelian` is the **abelian case of the Chebotarev density theorem** — the
analytic kernel that the general theorem reduces to (pass to the cyclic fixed field
`E = L^⟨σ⟩` and push the density down), exactly as the literature presents the proof
(*general ⇐ abelian ⇐ cyclotomic*; MIT 18.785 L28, Stevenhagen–Lenstra, Di Meglio)
and exactly as the project layers `Main` ⇐ `Abelian` ⇐ `Cyclotomic`. Mathlib has
none of this: an exhaustive grep over the vendored tree returns zero hits for
Chebotarev/Cebotarev, zero for any Dirichlet/analytic density of prime ideals, and
zero for Frobenius equidistribution; the nearest neighbour
`Nat.infinite_setOf_prime_and_eq_mod` is, by its own docstring, *infinitude only* and
only for the `K=ℚ`/cyclotomic special case. The gap is total and on-the-roadmap: FLT
records Chebotarev as a needed dependency and PNT+ as a stretch goal. The statement
is, moreover, exactly the literature-standard abelian case at its canonical
generality (finite abelian Galois extension of number fields, Dirichlet density,
per-element `σ`, value `1/|G|`), written in fully modern mathlib idiom — the abelian
hypothesis is mathlib's own `IsMulCommutative` mixin, density is the filter-based
`Tendsto … (𝓝[>] 1)`. There is no weaker hypothesis set this proof supports: dropping
`IsMulCommutative` is not a weakening of this proof but the *strictly harder* general
Chebotarev (which **consumes** this lemma — the wrong direction for "generalise
first"), and the natural/effective-density and global-field strengthenings are
separate analytic developments. So the verdict is add-as-is, not generalise-first.

The 2 internal call sites are the textbook "real API root" pattern: this is the
output the rest of the development sits on (general Chebotarev at Main.lean:87, the
bundled commutative restatement at Main.lean:110), with no bypass re-derivation — so
the YES is reinforced, not weakened, by the call-site analysis.

**The one real subtlety** is packaging, not mathematical content (shared with the
`chebotarev_density` / `dirichlet_primes_in_AP` assessments): the theorem is phrased
via the three *project* definitions `HasDirichletDensity`, `frobeniusClass`,
`UnramifiedIn`, none of which exists in mathlib. Mathlib will want those promoted to
canonical definitions (each with its own `def`-level diamond/defeq and naming review)
**before or together with** this theorem. That is sequencing, not a downgrade: the
theorem is the right statement; it travels with its definitional prerequisites.
(Mathlib already has the Frobenius *element* `arithFrobAt`, so `frobeniusClass` is a
thin well-founded wrapper; `HasDirichletDensity` is the substantial new definition.)

**WHY add it (refactor-actionable):**
- *New mathematical content mathlib is missing:* the **abelian case of Chebotarev** —
  the per-element Frobenius-equidistribution density `1/|G|` for an abelian Galois
  extension — together with (as its definitional substrate) the entire analytic
  density-of-prime-ideals layer (`HasDirichletDensity` + the `s→1⁺` Dedekind-zeta
  ratio asymptotics). Mathlib today has **no** Dirichlet/analytic density of prime
  ideals at all, and **no** Chebotarev in any case.
- *The specific gap, named:* Chebotarev (and a fortiori its abelian case, the stage
  everything reduces to) is a declared dependency of the **FLT project** ("a version
  of it is needed for the proof of FLT") and a declared **stretch goal of PNT+**
  (Tao/Kontorovich). Two flagship efforts have it on the roadmap; neither has landed
  it. This is the gap. (Broader: this is the same analytic-density layer the sibling
  `dirichlet_primes_in_AP` needs to refine mathlib's infinitude-only
  `Nat.infinite_setOf_prime_and_eq_mod` into a density statement.)
- *How it composes with mathlib:* it sits directly on `NumberField.DedekindZeta`,
  `RingTheory.Frobenius.arithFrobAt`, `ConjClasses`/`Nat.card`, and
  `IsMulCommutative`; once present it is the analytic core from which the general
  `chebotarev_density` (via the fixed-field reduction), its corollary
  `density_split_completely`, and the named `dirichlet_primes_in_AP` all follow.

**Proposed mathlib location:**
`Mathlib/NumberTheory/NumberField/Chebotarev.lean` (with the abelian/cyclotomic core
possibly in a companion `Mathlib/NumberTheory/NumberField/ChebotarevAbelian.lean`),
the density layer in `Mathlib/NumberTheory/NumberField/DirichletDensity.lean`
(the `HasDirichletDensity` def + Dedekind-zeta `s→1⁺` asymptotics), and the
Frobenius-class wrapper near `Mathlib/RingTheory/Frobenius.lean` / a new
`Mathlib/NumberTheory/NumberField/FrobeniusClass.lean`.

**Proposed PR title:**
`feat(NumberTheory): Chebotarev's density theorem, abelian case`

**PR grouping (required — ship within the Chebotarev chain):** this is the analytic
core that the general theorem reduces to; it cannot be stated without
`HasDirichletDensity` / `frobeniusClass` / `UnramifiedIn` and is itself built on the
cyclotomic case. Per the sibling `chebotarev_density.md` plan, the chain is:
1. `feat(NumberTheory): Dirichlet density of a set of prime ideals` — the
   `HasDirichletDensity` def + Dedekind-zeta `s→1⁺` asymptotics (`Density.lean`).
2. `feat(NumberTheory): Frobenius conjugacy class of an unramified prime`
   (`Frobenius.lean`) — `UnramifiedIn` + `frobeniusClass` on `arithFrobAt`.
3. `feat(NumberTheory): Chebotarev abelian/cyclic case` — **this theorem**, plus
   `liminf_ratio_ge_inv_card_G`, `ratioSum_frobeniusFibres_tendsto_one`, and the
   cyclotomic machinery (`Abelian.lean`, `FixedFieldDensity.lean`, `Cyclotomic.lean`).
4. `feat(NumberTheory): Chebotarev's density theorem` + corollaries
   `density_split_completely` and `dirichlet_primes_in_AP` — the capstone PR
   (consumes this one via the fixed-field reduction).

The single-declaration verdict here is YES-add-as-is; in practice it ships as PR (3),
the analytic core, after the definition layers (1)–(2) and before the capstone (4).

**Pre-PR checklist before opening:**
- [ ] `/generalise Chebotarev.chebotarev_abelian` — confirm no easy weakening
      (expected: none; dropping `IsMulCommutative` is the *separate* general
      theorem, and the per-subset form is a one-line corollary — record both).
- [ ] `/mathlibable` the three supporting **defs** (`HasDirichletDensity`,
      `frobeniusClass`, `UnramifiedIn`) individually — each needs a Phase-4.5
      diamond/defeq pass before upstreaming (this theorem-level run skipped 4.5).
- [ ] `/cleanup` the files in the PR chain (style audit + diff gates); in
      particular fold the pure real-analysis glue
      (`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` and the
      `LiminfSumGlue` section, Abelian.lean:1436–1474) — that block is independently
      mathlib-able as `Order`/`Topology` API and may upstream separately/earlier.
- [ ] Pick a reviewer from recent `Mathlib/NumberTheory/NumberField/` and
      `Mathlib/NumberTheory/LSeries/` committers (PrimesInAP authors: Stoll /
      Loeffler); coordinate with the FLT / PNT+ maintainers (Buzzard / Kontorovich),
      who want exactly this.

---

## Next step

YES-add-as-is. Upstream as **PR (3) — the abelian/cyclic analytic core** — of the
Chebotarev chain (see `chebotarev_density.md`): land the `HasDirichletDensity`
definition layer (PR 1) and the `frobeniusClass`/`UnramifiedIn` layer (PR 2) first,
then ship `chebotarev_abelian` together with `liminf_ratio_ge_inv_card_G`,
`ratioSum_frobeniusFibres_tendsto_one`, and the cyclotomic machinery, ahead of the
capstone `chebotarev_density` (PR 4) which reduces to it via the fixed field. Before
opening: `/mathlibable` the three supporting defs, then `/generalise` (expect no
weakening) and `/cleanup` the chain; consider splitting the `LiminfSumGlue`
real-analysis lemmas out as standalone `Order`/`Topology` API.
