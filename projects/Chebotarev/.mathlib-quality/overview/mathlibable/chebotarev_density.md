# /mathlibable report — `Chebotarev.chebotarev_density`

> Step-9 (overview) mathlibable assessment, run as the full 10-phase `/mathlibable`
> workflow on a single declaration. ChatGPT-math MCP was down (Codex command
> failed); the literature channel used the documented WebSearch + WebFetch + nLab
> fallback. Local Lean build is stale, so Phase 0b/5 rely on direct grep over the
> vendored mathlib source tree (`.lake/packages/mathlib/`), which is authoritative
> for "is it in mathlib".

---

## Phase 0 — Baseline

- lake build:               (stale — not rebuilt; reasoned from source per task note)
- decl `Chebotarev.chebotarev_density`:  resolved at
  `projects/Chebotarev/CebotarevDensity/Main.lean:71`
- **true qualified name:** `Chebotarev.chebotarev_density` (namespace `Chebotarev`
  opened at Main.lean:60; theorem at line 71). The parsed guess
  `Chebotarev.chebotarev_density` is **CORRECT**.
- kind:                      theorem
- has sorry:                 no (proof is complete: reduces to `chebotarev_abelian`
  via the fixed field `E = L^⟨σ⟩`)
- module docstring summary:  Chebotarev's density theorem in conjugacy-class form,
  with corollaries (Dirichlet primes in AP; density of completely split primes).

---

## Phase 1 — Statement (prose)

`Chebotarev.chebotarev_density` is **Chebotarev's density theorem in
conjugacy-class form**:

> Let `L/K` be a finite Galois extension of number fields with Galois group
> `G = Gal(L/K)`, and let `C ⊆ G` be a conjugacy class. Then the set of primes
> `𝔭` of `𝓞 K` that are unramified in `L` and whose Frobenius conjugacy class
> equals `C` has Dirichlet density `|C| / |G|`.

This is the central equidistribution theorem of algebraic number theory — the
non-abelian generalisation of Dirichlet's theorem on primes in arithmetic
progressions, and (its abelian case being class field theory) the qualitative
heart of the splitting-of-primes story.

**Variables / typeclasses (Lean side):**
- `{K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]` — the two
  number fields.
- `[Algebra K L] [IsGalois K L]` — `L/K` is a Galois extension.
- `[FiniteDimensional K L]` — finite extension (so `G` is finite).
- `(C : ConjClasses Gal(L/K))` — the target conjugacy class.

**Conclusion (math):** the Frobenius-fibre over `C` has Dirichlet density
`|C|/|G|`.

**Conclusion (Lean):**
```
HasDirichletDensity
  {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}
  ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K))
```
where the three ingredients are project definitions:
- `HasDirichletDensity S δ` (`Density.lean:64`) := the ratio of partial Dirichlet
  series `(Σ_{𝔭∈S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})` tends to `δ` as `s ↓ 1⁺` — the
  analytic (Dirichlet) density.
- `frobeniusClass K L 𝔭` (`Frobenius.lean:188`) := the conjugacy class of the
  arithmetic Frobenius `arithFrobAt (𝓞 K) Gal(L/K) 𝔓` for any `𝔓 ∣ 𝔭`
  (well-defined for unramified nonzero `𝔭`).
- `UnramifiedIn K L 𝔭` (`Frobenius.lean:62`) := `𝔭 ≠ ⊥` and every maximal prime
  above it is unramified.

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)
**Verdict: BIG.** Three independent triggers fire:
1. It is a **theorem named after a person** (Chebotarev / Cebotarev).
2. It is the **primary main result** of the project (`## Main results`, first
   bullet of the Main.lean docstring).
3. It is a recognised, named landmark theorem essentially guaranteed to be in the
   literature in some form.

### One-line check (Phase 2b)
n/a — kind is `theorem`, not a `def`. (Body is a ~16-line proof, not a one-liner.)

---

## Phase 3 — Literature search (EXHAUSTIVE)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Chebotarev density theorem conjugacy class Frobenius Dirichlet density" | yes | set of primes with Frobenius class `C` has Dirichlet density `|C|/|G|`, `|G|=[L:K]` | Wikipedia, EoM, Lenstra notes, Stevenhagen–Lenstra — **exact match to the Lean form** |
| 2 | WebSearch (general form) | "Chebotarev … most general statement number field Galois … natural vs Dirichlet density" | yes | finite Galois ext of number fields; `d(S)=#C/#G`; non-abelian ⇒ Frobenius is a conjugacy class | MIT 18.785 L28, Wolfram; notes a *stronger* asymptotic-count (natural-density) form |
| 3 | WebSearch (named-after / Lean status) | "mathlib4 Chebotarev density theorem formalization Lean" | partial | — | "formalization still **in progress** as part of the FLT effort, **not** a completed addition to mathlib4" |
| 4 | WebSearch (project status) | "Chebotarev … Lean mathlib FLT Buzzard status 2025 2026 ongoing not yet" | yes | — | FLT project: "Fermat will need Chebotarev Density Theorem" (a **needed dependency**, not yet done) |
| 5 | ChatGPT MCP | self-contained 3-part standard-form/generality/mathlib-status query | **n/a — MCP down** (Codex command failed) | — | fell back to WebSearch+WebFetch+nLab per the skill's documented fallback |
| 6 | Local references | `.mathlib-quality/references/` for the project | **n/a — directory absent** | — | no refs dir; PDFs are local-only (Sharifi `algnum.pdf`, SL `cheb.pdf`) and not present in this checkout |
| 7 | nLab | `Chebotarev density theorem` page | n/a — **404** | — | nLab has no dedicated page; concept is covered under class field theory / Frobenius |
| 8 | nCatLab / Stacks | "Stacks project Chebotarev density … Frobenius conjugacy class" | no (Stacks) | — | Stacks Project has no Chebotarev entry; not its scope. Not a categorical concept ⇒ nCatLab n/a |
| 9 | MathOverflow / Wikipedia "weak form" | (folded into #1/#2) | yes | "weak form": Frobenius-fibre is infinite with Dirichlet density `#A/n` | confirms the conjugacy-class Dirichlet-density statement is *the* standard weak form |
| 10 | recent arXiv (last 5y) | "Chebotarev density function field / global field generalization most general" | yes | holds for **any global field**; function-field case (Reichardt); effective/short-interval refinements | the strictly-more-general axis is global fields + effective error terms |

### Literature summary (Phase 3)

**Concept identified as:** the Chebotarev density theorem (conjugacy-class /
"weak" form).

**Sources agree on the standard form:** **yes.** Wikipedia, Encyclopedia of
Mathematics, MIT 18.785 (Lecture 28), Stevenhagen–Lenstra, and Lenstra's notes
all give exactly: *for a conjugacy class `C` in `Gal(L/K)`, the set of primes of
`K` unramified in `L` with Frobenius class `C` has density `|C|/|G|`*. This is
verbatim the Lean statement.

**Most general standard form:** over an arbitrary **global field** (number fields
and function fields over `𝔽_q`), with two density flavours:
- **Dirichlet (analytic) density** — the `s→1⁺` ratio limit. This is what the
  project formalises (`HasDirichletDensity`).
- **Natural density** + **asymptotic count** (`N_C(x) ∼ (|C|/n)·x/log x`) — the
  "strong form". Strictly stronger (natural density ⇒ Dirichlet density), needs
  PNT-type analytic input.

**Generality dimensions where the literature varies:**
- *Base field*: number field ⊊ global field (function fields added by Reichardt).
  The number-field case is the canonical textbook statement and the one FLT needs.
- *Density notion*: Dirichlet density (weakest, cleanest, no error term) ⊊ natural
  density ⊊ effective/quantitative (error terms, GRH-conditional bounds).
- *Conjugacy set*: a single class `C` vs. a union of classes (a conjugation-stable
  subset `C ⊆ G`); these are trivially interchangeable (sum over classes).

**Disagreement with the literature:** **none.** The Lean form is the literature
weak form at its most common generality (number fields, Dirichlet density, single
conjugacy class).

---

## Phase 4 — Generality analysis

**Literature-standard form (from Phase 3):** Chebotarev for a finite Galois
extension of **global fields**, Dirichlet density `|C|/|G|`, for a
conjugation-stable subset `C ⊆ G`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K] [NumberField L]` | number fields | global fields (number + function) | yes (global fields) | **NO for this proof.** The function-field case is a genuinely different theorem with a different proof (Frobenius on a curve, no `s→1⁺` Dirichlet density via `DedekindZeta`). Number-field case is the canonical statement and the FLT-needed one. Generalising = a whole separate development, not a weakening of *this* proof. |
| 2 | `(C : ConjClasses Gal(L/K))` | single conjugacy class | conjugation-stable subset `C ⊆ G` | yes (union of classes) | CHEAP: sum the single-class statement over the classes in the subset. A corollary, not a reason to restate the core theorem. |
| 3 | `[IsGalois K L] [FiniteDimensional K L]` | finite Galois | finite Galois | no | exactly the standard hypotheses; `G` must be finite for `|C|/|G|` to make sense. |
| 4 | density notion (`HasDirichletDensity`) | Dirichlet density | Dirichlet (weak) or natural (strong) | the *strong* form is strictly stronger, not weaker | The strong form (natural density / asymptotic count) **implies** this; it is a strengthening requiring PNT-grade analytic input. Not a "weakening". |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** for the number-field / Dirichlet-density
statement — i.e. it is exactly the standard textbook theorem.

Number of weakening opportunities found: **0** genuine *weakenings*. The two
"more general" axes (global fields; natural density/asymptotic count) are
**different/stronger theorems**, not assumption-weakenings of this proof. The
single-class → stable-subset move is a one-line corollary, not a restatement.

Cost of "generalising" to global fields or natural density: **EXPENSIVE — needs
new ideas** (a separate function-field development; or PNT-grade analytic
machinery mathlib does not yet have). Per the skill's cost rule, this does **not**
downgrade the verdict and does **not** make it YES-but-generalise — these are
follow-on theorems, not a better statement of *this* result.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Downstream this enables |
|---|----------|----------|------------------------|-------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | **already done** | `IsGalois`, `NumberField`, `FiniteDimensional` are all typeclasses; `C` is a first-class `ConjClasses` term | already maximally idiomatic |
| 2 | sequences/metric → filters/topology? | yes — *already done* | density defined via `Tendsto … (𝓝[>] 1)` (filter form), not an ε-sequence | composes with all of mathlib's filter-limit API |
| 3 | construct an object → universal-property class? | no | — | the statement is a `Prop` about a density value; nothing to characterise universally |
| 4 | set-with-closure → bundled substructure? | no | — | `ConjClasses` is already the right bundled quotient; `Ideal` is already bundled |
| 5 | vector-space/field-specific → weaken typeclasses? | no | — | already at `NumberField`, the correct generality for the analytic proof |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorical statement |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary structure? | partial | the `C ⊆ G` (subset) form generalises the single-class index | corollary only; see 4a row 2 |

**Modern-idiom verdict: no further modernisation move available.** The statement
already uses the contemporary mathlib idioms (typeclass hypotheses, filter-based
`Tendsto` density, `ConjClasses`, `arithFrobAt` from `RingTheory.Frobenius`). The
only "more general" reformulation (`HasDirichletDensity` for a conjugation-stable
subset rather than a single class) is a thin corollary worth shipping *alongside*,
not a reason to restate the theorem. One genuine API-surface note for the eventual
PR: mathlib will likely want `HasDirichletDensity` itself (and `frobeniusClass`,
`UnramifiedIn`) promoted as the canonical definitions first — see Phase 7.

---

## Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (no definitional equalities / typeclass-search
paths introduced). Skipped.

> Caveat carried to Phase 7: the *supporting definitions* `HasDirichletDensity`,
> `frobeniusClass`, `UnramifiedIn` are `def`s and would each warrant their own
> Phase-4.5 pass when *they* are upstreamed. They are out of scope for this
> single-declaration (theorem) assessment but are flagged as the real
> prerequisite work.

---

## Phase 5 — Mathlib search (five-method)

```
### Mathlib search-status: Chebotarev.chebotarev_density

[A] Lean-Finder       (MCP unavailable in this env)         n/a — tool not loadable; substituted grep [D]
[B] Loogle            (MCP unavailable in this env)          n/a — tool not loadable; substituted grep [D]
[C] LeanSearch        (MCP unavailable in this env)          n/a — tool not loadable; substituted grep [D] + WebFetch of mathlib docs
[D] Grep mathlib src  "chebotarev|cebotarev"                 NO HITS in .lake/packages/mathlib/
                      "DirichletDensity|dirichlet.density|analyticDensity"   NO HITS
                      "density.*prime|prime.*density|equidistribut"          NO HITS (no analytic prime-density infra)
                      "frobeniusClass|frobenius_class"        NO HITS
                      "arithFrobAt|IsArithFrobAt"             HIT: RingTheory/Frobenius.lean (building block only)
                      "ConjClasses.*carrier card"             HIT: GroupTheory/ClassEquation.lean (|C| building block only)
[E] Name pattern      (lean_local_search unavailable; grep over project + mathlib used)
```

**Searched for both forms:**
- *User's form* (Dirichlet-density conjugacy-class Chebotarev): not in mathlib.
- *Literature-standard / more general forms* (global-field Chebotarev; natural-
  density asymptotic count; any "density of primes with Frobenius in C"): not in
  mathlib. The closest analytic-NT result, `Nat.infinite_setOf_prime_and_eq_mod`
  (`NumberTheory/LSeries/PrimesInAP.lean`), is **infinitude only, not density** —
  confirmed by fetching the mathlib docs page.

**Cross-check against external project status:**
- **FLT project** (ImperialCollegeLondon/FLT): Chebotarev is listed as a *needed
  dependency* ("Fermat will need Chebotarev Density Theorem") — i.e. not yet
  available to import.
- **PNT+ project** (Tao/Kontorovich, PrimeNumberTheoremAnd): Chebotarev is an
  explicit *stretch goal* — "A stretch goal would be to obtain the Chebotarev
  density theorem." Not yet formalised.

**Concluded:** **not in mathlib** (all available search methods exhausted, plus
the literature-standard and more-general forms, plus the two flagship in-progress
projects that *want* it). Mathlib has only the building blocks
(`arithFrobAt`, `ConjClasses` cardinality via `ClassEquation`, `DedekindZeta`) and
the *infinitude* version of the Dirichlet-AP special case — never the density
statement, never Chebotarev.

---

## Phase 6 — Composition check (+ call-sites)

### 6.0. Call sites — `Chebotarev.chebotarev_density`

Internal use count: **2** (within the project, excluding the declaring site).
External-to-file callers: 0 distinct other files (both uses are in Main.lean, but
they are downstream *consumers*, not re-derivations).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `CebotarevDensity/Main.lean:133` | `infinite_of_hasDirichletDensity_pos (chebotarev_density C) ?_` — derives `infinite_setOf_frobenius_class` (infinitely many primes per Frobenius class) |
| `CebotarevDensity/Main.lean:156` | `have h := chebotarev_density (ConjClasses.mk (1 : Gal(L/K)))` — derives `density_split_completely` (density `1/[L:K]` of completely-split primes) |

Sibling/ecosystem use: `chebotarev_density_of_comm` (Main.lean:103, abelian case
re-statement) and `dirichlet_primes_in_AP` (Main.lean:517, Dirichlet AP as a
density refinement) are built from the same machinery (`chebotarev_abelian` /
`chebotarev_cyclotomic`). So `chebotarev_density` is a genuine API **root** with
multiple proper consumers — the strongest "real API" composability signal.

Inline-derivation grep (was the statement re-derived elsewhere without the
lemma?): **none.** No file re-proves `|C|/|G|` density by hand; everything routes
through this theorem or its abelian/cyclotomic kernels.

### 6a. Composition attempt

Can `chebotarev_density` be derived from **mathlib** in ≤3 chained calls?

- **Attempt 1:** any mathlib density/equidistribution lemma → **fails at step 0**:
  mathlib has no density-of-primes / Chebotarev / Frobenius-equidistribution lemma
  to chain from (Phase 5).
- **Attempt 2:** assemble from `arithFrobAt` + `DedekindZeta` + `ClassEquation`
  → **fails**: this is not a 1–3 call composition; it is the entire proof. The
  project proof itself is a non-trivial reduction (pass to the fixed field
  `E = L^⟨σ⟩`, invoke the cyclic/abelian case `chebotarev_abelian`, and run a
  counting argument `density_lift_through_fixedField`), and `chebotarev_abelian`
  is itself a large multi-file development (Abelian.lean is 1500+ lines). The
  building blocks exist; the *theorem* is hundreds of lines of new mathematics.

**Conclusion: NOT-COMPOSABLE.** This is the canonical "mathlib has the bricks, not
the building" case — and the building is large.

---

## Phase 7 — Verdict

## Verdict: `Chebotarev.chebotarev_density`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): the conjugacy-class Dirichlet-density form `|C|/|G|`
  is *the* standard textbook ("weak form") statement, agreed across Wikipedia, EoM,
  MIT 18.785 L28, Stevenhagen–Lenstra, Lenstra; the Lean form matches verbatim.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for the number-field /
  Dirichlet-density statement; the only "more general" axes (global fields; natural
  density) are *different/stronger* theorems, not weakenings (cost EXPENSIVE,
  non-downgrading per the rules). Modern-idiom check: already idiomatic
  (typeclasses, filter `Tendsto` density, `ConjClasses`, `arithFrobAt`).
- Mathlib search (Phase 5): not in mathlib by any method; only building blocks
  present; the two flagship projects (FLT, PNT+) list it as a wanted-but-unfinished
  target.
- Composition check (Phase 6): NOT-COMPOSABLE — it is a large multi-file proof, not
  a ≤3-call composition; and it is a real API root with 2 internal consumers and no
  inline re-derivation.

**Rationale.**
Chebotarev's density theorem is a named landmark of algebraic number theory and is
flatly absent from mathlib: an exhaustive grep over the vendored mathlib tree
returns zero hits for Chebotarev, for any Dirichlet/analytic density of prime
ideals, and for any Frobenius equidistribution; the nearest neighbour
(`Nat.infinite_setOf_prime_and_eq_mod`) gives only *infinitude* of primes in an AP,
not density. The gap is not incidental — it is actively sought: the FLT project
records "Fermat will need Chebotarev Density Theorem" and the Tao–Kontorovich PNT+
project lists Chebotarev as an explicit stretch goal. So this is the rare case
where a project decl is both a recognised theorem and a named, on-the-roadmap hole
in mathlib. The statement is, moreover, exactly the literature-standard weak form
at its canonical generality (finite Galois extension of number fields, Dirichlet
density, conjugacy class `C`, value `|C|/|G|`), stated in fully modern mathlib
idiom. There is no weaker hypothesis set that this proof supports, and the genuinely
more general statements (global fields; natural density / asymptotic count) are
separate developments rather than reformulations — so the verdict is add-as-is, not
generalise-first.

**The one real subtlety** is packaging, not mathematical content: the theorem is
stated in terms of three *project* definitions — `HasDirichletDensity`,
`frobeniusClass`, `UnramifiedIn` — none of which exists in mathlib either. Mathlib
will want those promoted to canonical definitions (each with its own `def`-level
diamond/defeq and naming review) **before or together with** the theorem. That is
sequencing, not a downgrade: the theorem is the right statement; it simply travels
with its definitional prerequisites. (mathlib does have the Frobenius *element*
`arithFrobAt` in `RingTheory.Frobenius`, so `frobeniusClass` is a thin, well-founded
wrapper; `HasDirichletDensity` is the substantial new definition.)

**WHY add it (refactor-actionable):**
- *New mathematical content mathlib is missing:* the entire analytic
  density-of-prime-ideals layer (`HasDirichletDensity` and the `s→1⁺`
  Dedekind-zeta ratio asymptotics behind it) plus the Frobenius-conjugacy-class
  equidistribution theorem on top of it. Mathlib today has **no** notion of
  Dirichlet/analytic density of a set of prime ideals at all.
- *The specific gap, named:* Chebotarev is a declared dependency of the **FLT
  project** (Buzzard: "Fermat will need Chebotarev Density Theorem") and a declared
  **stretch goal of PNT+** (Tao/Kontorovich). Two flagship efforts have it on the
  roadmap and neither has landed it. This is the gap.
- *How it composes with mathlib:* it sits directly on top of
  `NumberField.DedekindZeta`, `RingTheory.Frobenius.arithFrobAt`,
  `GroupTheory.ClassEquation` (for `Σ|C| = |G|`), and `ConjClasses`; once present,
  it immediately yields Dirichlet's theorem on primes in AP *as a density statement*
  (the project's `dirichlet_primes_in_AP`, refining mathlib's infinitude-only
  `Nat.infinite_setOf_prime_and_eq_mod`) and the density of completely-split primes
  (`density_split_completely`).

**Proposed mathlib location:** `Mathlib/NumberTheory/NumberField/Chebotarev.lean`
(new file), with the density layer in
`Mathlib/NumberTheory/NumberField/DirichletDensity.lean` and the Frobenius-class
wrapper near `Mathlib/RingTheory/Frobenius.lean` / a new
`Mathlib/NumberTheory/NumberField/FrobeniusClass.lean`.

**Proposed PR title:** `feat(NumberTheory): Chebotarev's density theorem (conjugacy-class form)`

**PR grouping (required — this must NOT be a single PR):** ship as a *sequence*:
1. `feat(NumberTheory): Dirichlet density of a set of prime ideals` — the
   `HasDirichletDensity` definition + the Dedekind-zeta `s→1⁺` asymptotics
   (`Density.lean`). This is the load-bearing prerequisite and a `def`-level review.
2. `feat(NumberTheory): Frobenius conjugacy class of an unramified prime` —
   `UnramifiedIn` + `frobeniusClass` on top of `arithFrobAt` (`Frobenius.lean`).
3. `feat(NumberTheory): Chebotarev abelian/cyclic case` (`Abelian.lean`,
   `FixedFieldDensity.lean`, `Cyclotomic.lean`) — the analytic core.
4. `feat(NumberTheory): Chebotarev's density theorem` — **this theorem**, plus its
   corollaries `density_split_completely` and `dirichlet_primes_in_AP`.

The single-declaration verdict here is YES-add-as-is; in practice it upstreams as
the capstone of the 4-PR chain above, since it cannot be stated without (1)–(2)
and cannot be proved without (3).

**Pre-PR checklist before opening:**
- [ ] `/generalise Chebotarev.chebotarev_density` — confirm no easy weakening
      (expected: none beyond the single-class→stable-subset corollary; record it).
- [ ] `/mathlibable` the three supporting **defs** (`HasDirichletDensity`,
      `frobeniusClass`, `UnramifiedIn`) individually — they each need a Phase-4.5
      diamond/defeq pass before upstreaming (this theorem-level run skipped 4.5).
- [ ] `/cleanup` the files in the PR chain (style audit + diff gates).
- [ ] Pick a reviewer from recent `Mathlib/NumberTheory/NumberField/` and
      `Mathlib/NumberTheory/LSeries/` committers; coordinate with the FLT / PNT+
      maintainers (Buzzard / Kontorovich) since both projects want exactly this.

---

## Next step

YES-add-as-is. Open the upstreaming chain at the **definition** layer first:
`/mathlibable` (then `/generalise` + `/cleanup`) on `HasDirichletDensity`,
`frobeniusClass`, `UnramifiedIn`, then PR them ahead of the abelian core, and land
`chebotarev_density` (with `density_split_completely` and `dirichlet_primes_in_AP`)
as the capstone PR. Coordinate with the FLT and PNT+ maintainers, who have
Chebotarev on their roadmaps as a wanted dependency / stretch goal.
