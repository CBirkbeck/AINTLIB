# `/mathlibable` report — `PadicLFunctions.summable_iff_tendsto_cofinite_zero`

**Final verdict: `NO-mathlib-has-it`** — mathlib already has this result, in a *strictly more
general* form, and the project theorem's proof body is a literal one-token delegation to it.

---

### Baseline (Phase 0)

- lake build:               not re-run (build is stale/slow in this checkout per task note);
  **reasoned from source** — the declaration and every dependency were read directly. The proof
  body is a single mathlib reference whose target was located and read in full, so elaboration is
  established by inspection rather than by re-running `lake build`.
- decl `PadicLFunctions.summable_iff_tendsto_cofinite_zero`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:45`
- kind:                      theorem
- has sorry:                 no (proof body is `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f`)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — exp/log series
  on the convergence ball of a nonarchimedean complete normed `ℚ_[p]`-algebra field; this theorem
  is the supporting lemma "E1" used to discharge summability of those series.

Source of the declaration:

```lean
omit [NormedAlgebra ℚ_[p] L] in
/-- E1: in a complete ultrametric normed field, a family is summable iff it
tends to `0` along the cofinite filter. -/
theorem summable_iff_tendsto_cofinite_zero {ι : Type*} (f : ι → L) :
    Summable f ↔ Tendsto f Filter.cofinite (𝓝 0) :=
  NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f
```

with ambient context

```lean
variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]
```

(the `omit [NormedAlgebra ℚ_[p] L]` drops the algebra hypothesis for this theorem, so the operative
hypotheses are `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]`).

---

### Statement (Phase 1)

`PadicLFunctions.summable_iff_tendsto_cofinite_zero` is a theorem stating the following:

> Let `L` be a complete non-archimedean (ultrametric) normed field. A family `f : ι → L` indexed by
> an arbitrary type `ι` is unconditionally summable if and only if `f` tends to `0` along the
> cofinite filter on `ι` (equivalently: for every neighbourhood `U` of `0`, all but finitely many
> `f i` lie in `U`).

This is the ultrametric "null-family ⇔ summable" criterion — the hallmark fact of p-adic analysis
that makes convergence in a complete non-archimedean field far simpler than in ℝ or ℂ.

Variables / typeclasses involved (Lean side):
- `L` — the ambient field; carries `[NormedField L]`, `[IsUltrametricDist L]`, `[CompleteSpace L]`.
  Mathematical role: a complete non-archimedean normed field.
- `ι : Type*` — an arbitrary index type (no finiteness or countability assumption). Mathematical
  role: the index set of the family.
- `f : ι → L` — the family being tested for summability.

Hypotheses (Lean side):
- none beyond the typeclasses (no explicit hypothesis arguments).

Conclusion (math): A family over a complete non-archimedean field is summable iff it is a null
family (cofinite-filter limit `0`).

Conclusion (Lean): `Summable f ↔ Tendsto f Filter.cofinite (𝓝 0)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a supporting helper lemma ("E1" in the project's decomposition) that re-states a mathlib
lemma at a more specific typeclass level; it is not a named theorem, not a new structure, and not a
primary project goal.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (the term `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the Phase 2b def-exemption table does not
apply to theorems/lemmas). Recorded as a one-line note per the skill: the proof is a one-token
delegation, which is itself the strongest possible signal that the content is not new.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic series converges iff terms tend to zero ultrametric Banach space" | yes | `∑ aₙ` converges ⇔ `aₙ → 0` in a complete non-archimedean field | Keith Conrad *Infinite Series in p-adic Fields*; Kedlaya *Ultrametric spaces* (18.727); Stoll *p-adic Analysis* notes; Pomerantz REU. Universally textbook. |
| 2 | WebSearch (general form) | "summable iff tends to zero cofinite filter nonarchimedean complete group" | yes | family `f : α → G` summable ⇔ tends to `0` on the cofinite filter, `G` complete nonarchimedean | matches the mathlib statement; cofinite = Fréchet filter (the complements-of-finite-sets filter). |
| 3 | WebSearch (named-after / aliases) | "nonarchimedean unconditional summability iff family tends to zero cofinite Bourbaki net" | yes | Encyclopedia of Mathematics *Unconditional summability*; net-of-finite-subsets formulation | "unconditional summability" / "summable family" / "null family" are the standard names; no person's name attached. |
| 4 | ChatGPT MCP | "standard definition + generality + historical evolution of the p-adic convergence criterion" | **n/a** | — | MCP server `chatgpt-math` is configured in the plugin `.mcp.json` but points to `/home/chris/.claude/mcp-servers/...` (a different machine); the tool is not surfaced in this environment. Compensated by extra WebSearch/WebFetch channels (#1–#3, #9). |
| 5 | Local references | check `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir) | both `.mathlib-quality/references/` and the gitignored `refs/` store are absent in this checkout — recorded n/a. (The module docstring itself cites Cassels §12, Washington *Cyclotomic Fields* §5.1, RJW Lem 5.14 as the surrounding-result sources.) |
| 6 | nLab | "summable family complete nonarchimedean group converges to zero" | yes | in a complete non-archimedean abelian group, a zero/null sequence is a summable family (Cauchy criterion over finite subsets); condensed-math "summable sequences = null-sequences" | confirms the general (filter/net) form; nLab `cofinite topology` page confirms the cofinite-filter object. |
| 7 | nCatLab (if categorical) | — | n/a | — | not a categorical concept; nLab (#6) already covers the abstract statement. |
| 8 | Stacks Project (if alg geom) | — | n/a | — | not an algebraic-geometry concept (analysis/topology of summable families). |
| 9 | MathOverflow / Math.StackExchange / arXiv | "double series over a non-Archimedean field"; "Algebraization of infinite summation"; condensed-math summable=null | yes | arXiv 1403.3623 (double series over non-arch fields), 2508.14290 (algebraization of summation) reaffirm the ultrametric criterion and its filter/net packaging | corroborates #2/#6; the result is folklore-canonical, restated in many sources. |
| 10 | recent arXiv (last 5 years) | condensed mathematics "summable sequences are the null-sequences" (Clausen–Scholze solid abelian groups) | yes | the solid-abelian-groups development takes exactly "summable = null" in the non-arch setting as foundational | modern reframing; the cofinite-filter form is the mathlib idiom of the same fact. |

#### Literature summary (Phase 3)

Concept identified as: **the non-archimedean / ultrametric summability criterion** — "a family in a
complete non-archimedean abelian group is (unconditionally) summable iff it is a null family
(tends to `0` along the cofinite filter)". Specialized to a field: "a p-adic series converges iff
its terms tend to `0`."

Sources agree on the standard form: **yes**. Every p-adic-analysis source (Conrad, Kedlaya, Stoll,
Pomerantz, Encyclopedia of Mathematics) states the sequence version `∑ aₙ` converges ⇔ `aₙ → 0`;
nLab and the condensed-mathematics literature state the arbitrary-index/family version (null family
⇔ summable), which is the cofinite-filter statement.

Most general standard form: **a complete non-archimedean (Hausdorff) abelian group `G`, an arbitrary
index set `α`, family `f : α → G`: `Summable f ↔ Tendsto f cofinite (𝓝 0)`.** Field structure,
norm, and a base ring are all unnecessary; only the additive group, its non-archimedean topology,
and completeness are used.

Generality dimensions where the literature varies:
- ambient object: from "complete non-arch *field*" (Conrad et al., sequence version) up to "complete
  non-arch *abelian group*" (nLab / condensed math, family version). The most general is the group.
- index set: from `ℕ`-indexed *sequences* (classical) up to *arbitrary index sets / families* via
  the cofinite filter (Bourbaki/filter form). The most general is the arbitrary index.

Disagreement with the literature: **none**. The project's statement is a faithful instance of the
standard form, merely pinned to a narrower ambient type (an ultrametric normed field) and using the
already-modern cofinite-filter phrasing.

---

### PHASE 4 — Generality analysis

Literature-standard (most general) form, from Phase 3: complete non-archimedean **additive abelian
group** `G`, arbitrary index `α`, `f : α → G`: `Summable f ↔ Tendsto f cofinite (𝓝 0)`.

#### Generality status table (Phase 4a)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]` | complete non-arch normed *field* | non-arch additive abelian *group* | **yes** | neither multiplication, inverses, nor a norm are used; only the additive topological-group structure + completeness. Mathlib's general form drops to `[CommGroup]`/`[AddCommGroup]` + `[UniformSpace]` + `[IsUniformAddGroup]` + `[NonarchimedeanAddGroup]`. |
| 2 | `[IsUltrametricDist L]` | metric ultrametric hypothesis | `[NonarchimedeanAddGroup G]` (topological, "every nbhd of 0 contains an open subgroup") | **yes** | the metric is inessential; the proof needs only the *topological* non-archimedean property. (`IsUltrametricDist` on a seminormed comm group *implies* `NonarchimedeanAddGroup` via `IsUltrametricDist.nonarchimedeanAddGroup`.) |
| 3 | `[CompleteSpace L]` | complete | complete (`[CompleteSpace G]`) | NO | completeness is essential (the Cauchy partial sums must converge); kept in mathlib's form too. |
| 4 | `(f : ι → L)`, `ι : Type*` | arbitrary index | arbitrary index | already maximal | no finiteness/countability assumed; same as standard. |

#### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (rows 1 and 2 are strictly stronger than the
literature/mathlib form).

Number of weakening opportunities found: 2 (field → additive group; ultrametric-metric →
topological non-archimedean).

Proposed restatement (the maximally general form):

```lean
theorem summable_iff_tendsto_cofinite_zero
    {α G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [NonarchimedeanAddGroup G] [CompleteSpace G] (f : α → G) :
    Summable f ↔ Tendsto f Filter.cofinite (𝓝 0)
```

Cost of restatement: **CHEAP (vacuous)** — this exact maximally-general statement *already exists in
mathlib* (see Phase 5), so there is nothing to re-prove. The narrowing is a pure typeclass
specialization, which is why the project's proof body is the single token
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f`.

Because the more general form **already exists in mathlib**, the verdict is NOT
`YES-but-generalise-first` (there is nothing to contribute). It is `NO-mathlib-has-it`: the project
should delete its specialization and call the mathlib lemma. See Phase 7.

#### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "Let X be a foo" preambles → typeclasses/instances? | no | — | already fully typeclass-driven. |
| 2 | sequences/metric → filters/nets/topological? | **already done** | the statement is *already* in the modern filter idiom (`Tendsto f cofinite (𝓝 0)`), and the *more general* version drops the metric (`IsUltrametricDist`) for the topological `NonarchimedeanAddGroup`. | this modernisation is exactly what mathlib's `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` already realises. |
| 3 | construct object → universal-property class? | no | — | no object constructed; it is an iff. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | no substructure here. |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | **yes** | field → `AddCommGroup` + topological non-arch (rows 1–2 of 4a) | — but mathlib has already done this weakening; no new contribution. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | already maximal | index is already an arbitrary `Type*` | n/a. |

#### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no new one** — the *contemporary mathlib form* (filter phrasing +
`NonarchimedeanAddGroup` typeclass over an abelian group) is precisely what mathlib already ships.
The project theorem is a strictly narrower specialization of that already-modern form; there is no
modernisation left for the project to contribute. One-line reason: the modern idiom is the existing
mathlib lemma, not anything novel here.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`** (no definitional equalities or typeclass-search paths
introduced).

---

### PHASE 5 — Mathlib search

#### Five-method search-status: `PadicLFunctions.summable_iff_tendsto_cofinite_zero`

```
[A] Lean-Finder       "summable iff tends to zero cofinite nonarchimedean"   external web tool — not invocable in this sandbox; recorded n/a. Methods D + E below are decisive.
[B] Loogle            `Summable ?f ↔ Tendsto ?f Filter.cofinite (𝓝 0)`        n/a (web service not invocable here); the type pattern is matched by the grep hit in [D].
[C] LeanSearch        "p-adic / nonarchimedean series summable iff terms tend to zero"  n/a (web service not invocable here); covered by [D].
[D] Grep mathlib src  grep -rn "summable_iff_tendsto_cofinite_zero" .lake/packages/mathlib/   HIT (see below)
[E] Name pattern      grep "multipliable_iff_tendsto_cofinite_one", "summable_of_tendsto_cofinite_zero"  HIT (the to_additive source + its companions)
```

Searched for both:
- the user's current form (ultrametric normed field) — and
- the literature-standard / more general form (complete non-archimedean abelian group). The general
  form is exactly what mathlib has.

**Found in mathlib as `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`.** It is the
`@[to_additive]`-generated additive version of `NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one`,
declared at `.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:103`:

```lean
namespace NonarchimedeanGroup
variable {α G : Type*}
variable [CommGroup G] [UniformSpace G] [IsUniformGroup G] [NonarchimedeanGroup G]

@[to_additive /-- Let `G` be a complete nonarchimedean additive abelian group. Then a function
`f : α → G` is unconditionally summable if and only if it tends to zero on the filter of cofinite
sets. -/]
theorem multipliable_iff_tendsto_cofinite_one [CompleteSpace G] (f : α → G) :
    Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨Multipliable.tendsto_cofinite_one, multipliable_of_tendsto_cofinite_one⟩
```

The generated additive declaration has signature (additivising `CommGroup → AddCommGroup`,
`IsUniformGroup → IsUniformAddGroup`, `NonarchimedeanGroup → NonarchimedeanAddGroup`, `1 → 0`):

```lean
theorem NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero
    {α G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [NonarchimedeanAddGroup G] [CompleteSpace G] (f : α → G) :
    Summable f ↔ Tendsto f cofinite (𝓝 0)
```

Corroborating mathlib usages of the same lemma (confirming the generated name is real and live):
- `.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:119` —
  `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero] at *`
- `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/MahlerBasis.lean:287` — uses the companion
  `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.

The instance chain that makes the specialization land: `[NormedField L]` gives
`SeminormedAddCommGroup L` (hence `UniformSpace`/`IsUniformAddGroup`), and
`[IsUltrametricDist L]` + that comm-group structure gives `NonarchimedeanAddGroup L` via the mathlib
instance `IsUltrametricDist.nonarchimedeanAddGroup` (the `to_additive` of
`IsUltrametricDist.nonarchimedeanGroup`, `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Ultra.lean:197`).
With `[CompleteSpace L]`, mathlib's hypotheses are met exactly — which is why the project proof body
is just `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f` with no glue.

Concluded: **found in mathlib as `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`; more
general form (the project's is a pure typeclass specialization to an ultrametric normed field).**

---

### PHASE 6 — Composition check (+ call-sites signal)

#### Call sites — `PadicLFunctions.summable_iff_tendsto_cofinite_zero`

Internal use count (within the project, NOT counting the declaring file): **0**
External-to-file callers of the *project wrapper*: **0 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| PadicExp.lean:102 (declaring file) | `rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop, …]` |
| PadicExp.lean:355 (declaring file) | `rw [summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop, …]` |
| PadicExp.lean:767 (declaring file) | `rw [summable_iff_tendsto_cofinite_zero, NormedAddGroup.tendsto_nhds_zero]` |

So the wrapper is used 3× **inside its own file only**; it has **zero** consumers in any other file.

Inline-derivation grep (was the equivalent re-derived elsewhere *without* using the project
wrapper?): **YES — pervasively.** Every consumer outside `PadicExp.lean` calls the mathlib lemma
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` directly, bypassing the wrapper:

| Site bypassing the wrapper (calls mathlib lemma directly) | Excerpt |
|-----------------------------------------------------------|---------|
| PadicLFunctions/ResidueZeta.lean:1139 | `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, …]` |
| PadicLFunctions/MeasureR/FormalPsi.lean:800, 845, 956, 977 | `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, …]` (×4) |
| PadicLFunctions/IwasawaProof/GaloisAction.lean:752 | `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, …]` |
| AdicSpaces/Adic spaces/LaurentCoverExact.lean:1057 | `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]` |
| AdicSpaces/Adic spaces/GeometricSeries.lean:38 | `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]` |

Composability signal (per the Phase 6.0.1 table): **K = 0 external uses BUT the same statement is
re-derived inline (via the mathlib lemma) at ≥1 site** — in fact at 8 sites across two projects. This
is the textbook "wrapper that consumers bypass; mathlib has it" pattern → leans **NO-mathlib-has-it**.

#### Composition check (Phase 6)

Can `PadicLFunctions.summable_iff_tendsto_cofinite_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f`
  - Mathlib decls used: `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` (one call).
  - Result: **succeeds** — this is literally the project's own proof body, and it is a single
    direct application of the mathlib lemma (no `.symm`, no `.trans`, no glue).
  - Notes: this is not even a "composition"; it is *the same lemma*, specialized by typeclass
    inference. The right resolution is therefore NO-mathlib-has-it (use the mathlib lemma directly),
    not NO-composable (which is for genuine 1–3-call assemblies of distinct building blocks).

Conclusion: **NOT-COMPOSABLE in the "assemble distinct primitives" sense — because no assembly is
needed: mathlib already states this exact theorem (more generally).** Phase 7 picks NO-mathlib-has-it.

---

## Verdict: `PadicLFunctions.summable_iff_tendsto_cofinite_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the result is the canonical ultrametric summability criterion; the
  arbitrary-index/cofinite-filter form over a complete non-archimedean abelian group is the standard
  general statement (nLab, condensed math, Encyclopedia of Mathematics; the sequence form is in
  every p-adic-analysis text — Conrad, Kedlaya, Stoll, Pomerantz).
- Generality analysis (Phase 4): **STRICTLY NARROWER** — the project pins the ambient to an
  ultrametric normed field; mathlib's form is over any complete non-archimedean `AddCommGroup`.
- Mathlib search (Phase 5): **found in mathlib as `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`**
  (the `to_additive` of `NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one`,
  `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:103`), in a strictly more general form.
- Composition check (Phase 6): the project wrapper has **0 external-file consumers**; 8 sites across
  two projects already call the mathlib lemma directly, bypassing the wrapper.

**Rationale:**

This theorem is not new mathematics and not a new formulation — it is mathlib's own
`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, restricted from "complete
non-archimedean additive abelian group" down to "complete ultrametric normed field". The proof body
makes this unambiguous: it is the single token `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f`,
which typechecks because `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` produces mathlib's
hypothesis cluster through the instance `IsUltrametricDist.nonarchimedeanAddGroup`. There is no
generalisation to *contribute* (the general form is the one mathlib already has), so the verdict is
NO-mathlib-has-it rather than YES-but-generalise-first.

The call-site evidence is the clincher. The project wrapper is used only inside its own declaring
file (`PadicExp.lean`, 3 rewrites), and even one of those same-file rewrites (line 767) calls the
qualified mathlib name. Every other consumer — `ResidueZeta.lean`, `FormalPsi.lean` (×4),
`GaloisAction.lean` in PadicLFunctions, plus `LaurentCoverExact.lean` and `GeometricSeries.lean` in
the *separate* AdicSpaces project — already invokes `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`
directly. The repository has, in effect, already voted: the mathlib lemma is the canonical handle,
and the project wrapper is a thin local alias that consumers route around.

**WHY not (refactor-actionable):**
Mathlib already has this exact result, more generally. The named gap does not exist — to the
contrary, the mathlib lemma is *already* the form the rest of the repo uses. The project theorem
adds nothing but a narrower typeclass signature.

Existing mathlib decl:        `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`
Located at:                   `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean:103`
                              (generated by `@[to_additive]` from `multipliable_iff_tendsto_cofinite_one`;
                              live and used at `Nonarchimedean.lean:119` and `MahlerBasis.lean:287`).
Our form follows in 0 lines (it is the same lemma, specialized by instance resolution):
```lean
example {ι : Type*} (f : ι → L) :
    Summable f ↔ Tendsto f Filter.cofinite (𝓝 0) :=
  NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero f
```

Call sites in our project (from Phase 6.0): the project wrapper is referenced at 3 sites, all in the
declaring file `PadicExp.lean` (lines 102, 355, 767); 0 external-file consumers.

**Refactor plan:** delete `PadicLFunctions.summable_iff_tendsto_cofinite_zero` and update its 3
in-file `rw` sites to use the mathlib name directly:
- `PadicExp.lean:102` — `rw [summable_iff_tendsto_cofinite_zero, …]` →
  `rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, …]`
- `PadicExp.lean:355` — same substitution.
- `PadicExp.lean:767` — already partly mathlib-qualified; make the first rewrite
  `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` too.
No argument-order or implicit/explicit adjustment is needed: the mathlib lemma takes the family `f`
positionally, exactly as the wrapper does, and the typeclass instances are found automatically (the
8 existing direct-call sites across the repo already demonstrate this works). The wrapper has no
external consumers, so deletion breaks nothing outside `PadicExp.lean`. (Optionally, for readability,
keep a one-line `local notation`/abbreviation — but mathlib style and the existing repo usage favour
calling the lemma by its real name.)

Next action: delete the project theorem; rewrite the 3 in-file call sites to the mathlib lemma.

---

## Next step

Delete `PadicLFunctions.summable_iff_tendsto_cofinite_zero` from
`projects/PadicLFunctions/PadicLFunctions/PadicExp.lean` and update its 3 in-file `rw` sites
(lines 102, 355, 767) to use `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero` directly —
the form the rest of the repository already uses. No mathlib PR is warranted (mathlib already has
the more general lemma); this is a project-local cleanup. Caveat: as a one-line specialization, the
wrapper is harmless WIP — removing it is a `/cleanup`-style dedup task, not a correctness fix.
