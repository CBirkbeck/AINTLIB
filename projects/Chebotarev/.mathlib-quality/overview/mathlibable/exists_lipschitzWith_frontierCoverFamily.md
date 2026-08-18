# /mathlibable report — `Chebotarev.exists_lipschitzWith_frontierCoverFamily`

> Step-9 mathlibable assessment, single declaration. ForMathlib/ helper, author-earmarked
> for mathlib. Verdict below: **NO-composable-from-mathlib**.

## Baseline (Phase 0)

- lake build:               not re-run (local build known stale; reasoning from source, per task brief)
- decl `Chebotarev.exists_lipschitzWith_frontierCoverFamily`:
                            ✓ resolved at
                            `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:295`
- qualified name:           `Chebotarev.exists_lipschitzWith_frontierCoverFamily`
                            (namespace `Chebotarev`, opened at file line 79; base name as given — VERIFIED)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Lipschitz parametrization of the frontier of `normLeOne K` — finitely many
                            Lipschitz images of the unit cube cover the `realSpace` frontier
                            `normAtAllPlaces '' (normLeOne K)` (Gun–Ramaré–Sivaraman §3.3 input to the
                            effective lattice-point count).

## Statement (Phase 1)

`exists_lipschitzWith_frontierCoverFamily` asserts that the finite family of maps
`frontierCoverFamily K` admits a **single common Lipschitz constant**: there is one
`M : ℝ≥0` such that every member `frontierCoverFamily K s` is `M`-Lipschitz.

Here `frontierCoverFamily K` (defined at line 284) is indexed by the finite sum type
`Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)` and assembled by `Sum.elim`
into three kinds of map `(Fin (card (InfinitePlace K) − 1) → ℝ) → realSpace K`:
- `inl ()`              ↦ the constant zero map `fun _ ↦ 0`;
- `inr (inl ())`        ↦ `faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K` (the `w₀`-face);
- `inr (inr (i, b))`    ↦ `faceMapSide K i (if b then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K`
                          (a side face, `a ∈ {0,1}`).

`faceMapZero` / `faceMapSide` are `C¹` maps built on `expMapBasis` (a `NumberField`
`mixedEmbedding` object); `clampUnit` is the 1-Lipschitz coordinatewise retraction onto
`Icc 0 1`; `cubeRelabel` is a 1-Lipschitz coordinate relabelling.

The exact Lean form of the proof (lines 295–306):

```lean
theorem exists_lipschitzWith_frontierCoverFamily :
    ∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s) := by
  classical
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)
  choose Ms hMs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool ↦
    exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))
  refine ⟨M₀ ⊔ Finset.univ.sup Ms, fun s ↦ ?_⟩
  rcases s with _ | _ | p
  · exact (LipschitzWith.const _).weaken zero_le
  · exact (hM₀.comp (lipschitzWith_cubeRelabel K)).weaken (by rw [mul_one]; exact le_sup_left)
  · exact ((hMs p).comp (lipschitzWith_cubeRelabel K)).weaken
      (by rw [mul_one]; exact le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p)))
```

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K]` `[NumberField K]` — the base number field.

Hypotheses: none (all data is packed into `frontierCoverFamily K`).

Conclusion (math): the three-piece cube-cover family of the `normLeOne` frontier is
**uniformly Lipschitz** — one constant `M` works for every face map.

Conclusion (Lean): `∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s)`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: existence-of-uniform-constant helper feeding the next theorem
`normLeOne_frontier_lipschitz_cover`; not a `## Main results` headline, not named after a
person, introduces no structure. (Literature width still run EXHAUSTIVE below.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (Recorded; the
proof body is 6 lines of assembly, but the one-liner heuristic targets `def` bodies only.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "finite family of Lipschitz functions common uniform Lipschitz constant maximum"                       | yes  | sup/max of Lipschitz functions sharing a constant `K` is `K`-Lipschitz; bounded-Lipschitz family = equicontinuous | UTSA wiki, Wikipedia "Lipschitz continuity", Heinonen *Lectures on Lipschitz analysis* — all treat `M = max Kᵢ` as the trivial observation |
|  2 | WebSearch (general / mathlib)    | "mathlib4 LipschitzWith finite family uniform constant Finset.sup"                                      | yes  | mathlib `LipschitzWith.uniformEquicontinuous`; `LipschitzWith K f ↔ dist (f x)(f y) ≤ K·dist x y` | `Mathlib.Topology.MetricSpace.UniformConvergence`, `…EMetricSpace.Lipschitz`, `…MetricSpace.Lipschitz` docs. No packaged `∃ M, ∀ s, LipschitzWith M (g s)` lemma surfaced |
|  3 | WebSearch (source paper)         | "Gun Ramaré Sivaraman counting ideals ray classes Lipschitz boundary parametrization fundamental domain" | yes  | "compute the Lipschitz class of the boundary of the fundamental domain" (the §3.3 result, after Debaene) | HAL hal-03805062, arXiv:2208.06602, JNT 243 (2023). Confirms the *consumer* context, not a named lemma for the uniform-constant step |
|  4 | ChatGPT MCP                      | "is a finite family of Lipschitz maps admitting a common constant standard / named; does mathlib have `∃M,∀s,LipschitzWith M`?" | n/a  | — | MCP server down in this environment (Codex exec error); fell back to WebSearch + grep + nLab per task brief |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "Lipschitz"                                                     | n/a  | — | no `references/` dir under `projects/Chebotarev/.mathlib-quality/`; and `refs/Chebotarev/` absent in this checkout |
|  6 | nLab                             | "Lipschitz map" / "Lipschitz continuity"                                                                | n/a  | — | nLab has no "uniform constant over a finite family" page; the fact is folklore (`max` of finitely many reals), not an nLab-level concept |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | — | not a categorical statement (no universal property; finite-max of NNReal constants) |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | — | not an algebraic-geometry concept |
|  9 | MathOverflow / Math.SE           | folded into #1 ("common Lipschitz constant" wording)                                                    | yes  | same as #1: `max` of the constants; standard exercise-level fact | no distinct named theorem |
| 10 | recent arXiv (last 5 yrs)        | folded into #3 (the GRS paper is the relevant 2022 arXiv source)                                        | yes  | the boundary-Lipschitz-class computation is the application; uniform-constant step is implicit/trivial there | arXiv:2208.06602 |

### Literature summary (Phase 3)

Concept identified as: **uniform (common) Lipschitz constant for a finite family of Lipschitz
maps** — i.e. `M = maxₛ Kₛ` + monotonicity of the Lipschitz constant. The geometric envelope
(the *cube cover of the `normLeOne` frontier*) is the Gun–Ramaré–Sivaraman §3.3 / Debaene
"Lipschitz class of the boundary" construction, but **this specific lemma is only the
uniform-constant bookkeeping step inside that construction**, not the construction itself.

Sources agree on the standard form: yes — every source treats "finitely many `Kᵢ`-Lipschitz
maps ⇒ all `(max Kᵢ)`-Lipschitz" as the trivial max observation. No source gives it a name; it
is an immediate consequence of `LipschitzWith` monotonicity.

Most general standard form: for any finite (indeed any uniformly-bounded) family of
`Kᵢ`-Lipschitz maps, the common constant `sup Kᵢ` works; the family is then uniformly
equicontinuous.

Generality dimensions where the literature varies:
  - index set: finite → arbitrary with bounded constants (the sup exists). The user's index is a
    fixed finite sum type.
  - the *content* of each map: the literature step is map-agnostic; the user's three map kinds
    (`faceMapZero`, `faceMapSide`, const `0`) are project-specific `expMapBasis` faces.

Disagreement with the literature: none. The lemma is a correct, standard, **trivial** step;
the literature offers no more-general *named* target to aim at — the general fact is already
folklore and (its key half) already in mathlib.

## Generality analysis — `Chebotarev.exists_lipschitzWith_frontierCoverFamily`

Literature-standard form (from Phase 3): finite/bounded family of Lipschitz maps ⇒ common
constant `sup Kₛ`.

| # | Parameter / hypothesis                  | Current Lean form                         | Literature-standard form           | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------|-------------------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | the family `frontierCoverFamily K`      | one fixed project-specific `Sum.elim` of three `expMapBasis`-faces | *any* finite family `g : ι → (X → Y)` with each `g s` Lipschitz | yes (massively) | the statement is glued to a concrete project def; the general fact "`∀ s, ∃ K, LipschitzWith K (g s)` ⇒ `∃ M, ∀ s, LipschitzWith M (g s)`" over a `Fintype ι` is the real general statement — but see Phase 6: that general statement is itself a ≤3-call composition and is not what this lemma is |
| 2 | `[Field K] [NumberField K]`             | number field                              | irrelevant to the uniform-constant step | yes              | `K` enters only through the concrete faces; the uniform-constant principle has nothing to do with number fields |
| 3 | codomain `realSpace K`, finite-`Fin` domain | specific finite-dim ℝ-spaces          | any (pseudo-e)metric spaces        | yes              | `LipschitzWith` makes sense between any `PseudoEMetricSpace`s |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in a way that does **not** point
to a `YES-but-generalise-first`. The "general form" is not a generalised *version of this lemma*;
it is a *different, trivial, already-composable lemma* (`∃M,∀s,LipschitzWith M (g s)` from a
`Fintype` of per-index Lipschitz maps). Restating *this* lemma generally just **is** that
composable fact — at which point it dissolves into mathlib primitives (Phase 6), so the
generalisation target is "delete + inline", not "PR a generalised lemma".

Number of weakening opportunities found: 3 (all of the "this is really a special case of a
trivial general fact" kind).
Proposed restatement (the general fact, for the record):

```lean
theorem exists_lipschitzWith_of_forall {ι X Y : Type*} [Fintype ι]
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {g : ι → X → Y}
    (h : ∀ s, ∃ K : ℝ≥0, LipschitzWith K (g s)) :
    ∃ M : ℝ≥0, ∀ s, LipschitzWith M (g s) := by
  classical
  choose K hK using h
  exact ⟨Finset.univ.sup K, fun s ↦ (hK s).weaken (Finset.le_sup (Finset.mem_univ s))⟩
```

Cost of restatement: CHEAP (mechanical) — but the restatement is exactly the Phase-6
composition, i.e. it is itself NO-composable territory, not a mathlib-worthy new lemma.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                | no       | — | already typeclassed (`PseudoEMetricSpace`, `Fintype`) |
|  2 | sequences/metric → filters/topological?                                  | no       | — | `LipschitzWith` already the right metric-side notion; nothing to filterise |
|  3 | construct object → universal-property class?                             | no       | — | no object constructed; pure existence |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — | n/a |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                 | no       | — | the *general* fact is already as weak as `PseudoEMetricSpace`; this lemma's specificity is the concrete family, not over-strong typeclasses |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary groups/monoids?                       | no       | — | index is an abstract finite sum type already |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. There is no contemporary reformulation that turns this into a
mathlib-worthy contribution. The only "generalisation" is to strip the concrete family — which
yields the trivial `choose K; Finset.univ.sup K + weaken` composition, not a modernisation.

## Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities, no typeclass-search paths
introduced).

## Mathlib search-status: `Chebotarev.exists_lipschitzWith_frontierCoverFamily`

Search tools note: the dedicated lean MCP search tools (`lean_loogle` / `lean_leansearch` /
`Lean-Finder` / `lean_local_search`) are **not available** as callable tools in this environment
(ToolSearch returned no matches for them). Method D (grep over the local
`.lake/packages/mathlib/Mathlib/` tree) and WebSearch-against-mathlib-docs were used as the
substitutes and are recorded explicitly.

```
[A] Lean-Finder       —                                                  n/a: tool not available in this environment
[B] Loogle            (intended: `(?ι → ?X → ?Y) → ∃ _, ∀ _, LipschitzWith _ _`)  n/a: tool not available; substituted by [D]+WebSearch
[C] LeanSearch        (intended: "common Lipschitz constant for a finite family")  n/a: tool not available; substituted by WebSearch row 2
[D] Grep mathlib src  "exists_lipschitzWith", "Sum.elim.*Lipschitz", "Finset.sup.*Lipschitz",
                      "LipschitzWith.weaken/.comp/.const", "Finset.le_sup", "le_sup_left",
                      "LocallyLipschitzOn.exists_lipschitzOnWith_of_compact", "LipschitzWith.max",
                      "LipschitzWith.uniformEquicontinuous"                        see results below
[E] Name pattern      (intended: lean_local_search "exists_lipschitz", "uniform_lipschitz")  n/a: tool not available; substituted by [D] name grep
```

Method D (grep) results — searched for BOTH the user's form and the literature-standard form:

- `grep "theorem exists_lipschitzWith\|lemma exists_lipschitzWith\|def exists_lipschitzWith" Mathlib/`
  → **no hits.** Mathlib has **no** `exists_lipschitzWith…` lemma of any kind — in particular no
  packaged "finite family ⇒ uniform constant" existence lemma.
- `grep "Sum.elim.*Lipschitz\|Lipschitz.*Sum.elim" Mathlib/` → **no hits.**
- `grep "Finset.sup.*Lipschitz\|Lipschitz.*Finset.sup\|Finite.*exists.*LipschitzWith" Mathlib/`
  → **no hits.**
- Building blocks that DO exist (all cited by qualified name + file:line):
  - `LipschitzWith.weaken` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:172`
  - `LipschitzWith.comp` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:228`
  - `LipschitzWith.const` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:197`
  - `Finset.le_sup` — `Mathlib/Data/Finset/Lattice/Fold.lean:118`
  - `le_sup_left` — `Mathlib/Order/Lattice.lean:140`
  - `le_sup_of_le_right` — `Mathlib/Order/Lattice.lean:156`
  - `LipschitzWith.max` — `Mathlib/Topology/MetricSpace/Lipschitz.lean:177`
    (binary-max-preserves-constant; the abstract content of "common constant")
  - `LipschitzWith.uniformEquicontinuous` — `Mathlib/Topology/MetricSpace/UniformConvergence.lean:96`
    (the general "common-constant family is uniformly equicontinuous" lemma)
  - `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`
    — `Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean:58` (the per-face C¹-on-compact engine,
    already consumed via the project's `exists_lipschitzWith_comp_clampUnit`)

Concluded: **not in mathlib** (all available methods exhausted, both the user's form and the
general "finite family ⇒ uniform constant" form). The *building blocks* are all present; the
exact statement (and even the general statement) is a short composition of them.

## Call sites — `Chebotarev.exists_lipschitzWith_frontierCoverFamily`

Internal use count: **0** (within the project, excluding the declaring file).
External-to-file callers: **0 files**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | grep `grep -rn "exists_lipschitzWith_frontierCoverFamily" projects/ --include=*.lean` returns only the declaration line in `NormLeOneLipschitz.lean:295` |

Inline-derivation grep: the *only* consumer is the very next theorem in the same file,
`normLeOne_frontier_lipschitz_cover` (line 348), which calls
`obtain ⟨M, hM⟩ := exists_lipschitzWith_frontierCoverFamily K` (line 354). So it has exactly
**one in-file consumer** and zero out-of-file consumers. `frontierCoverFamily` itself likewise
has no uses outside the declaring file.

Signal (per the call-sites table in the verdicts reference): K = 0 external + a single in-file
consumer ⇒ "possibly the wrong abstraction / could be inlined; leans NO-composable." It is a
private-style scaffolding lemma for one local theorem.

## Composition check (Phase 6)

Can `exists_lipschitzWith_frontierCoverFamily` be derived from mathlib + the project's own
already-present face lemmas in ≤3 chained calls (per index case)?

Attempt 1 — reproduce the existence directly:
```lean
-- per the three Sum.elim cases, each is ≤3 mathlib/project calls:
--   inl ()        : (LipschitzWith.const _).weaken zero_le
--   inr (inl ())  : (hM₀.comp (lipschitzWith_cubeRelabel K)).weaken le_sup_left'
--   inr (inr p)   : ((hMs p).comp (lipschitzWith_cubeRelabel K)).weaken (Finset.le_sup …)
-- with M := M₀ ⊔ Finset.univ.sup Ms
```
- Mathlib decls used: `LipschitzWith.const`, `LipschitzWith.weaken`, `LipschitzWith.comp`,
  `Finset.le_sup`, `le_sup_left`, `le_sup_of_le_right`, `Finset.univ.sup`.
- Project decls used: `exists_lipschitzWith_comp_clampUnit`, `lipschitzWith_cubeRelabel`,
  `contDiff_faceMapZero`, `contDiff_faceMapSide` (these are *also* ForMathlib helpers in the same
  file — themselves thin wrappers over `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`).
- Result: **succeeds** — this IS the proof body (lines 298–306), and each branch is ≤3 calls.

Attempt 2 — the *general* version (strip the concrete family): `choose K hK; ⟨Finset.univ.sup K,
fun s ↦ (hK s).weaken (Finset.le_sup (Finset.mem_univ s))⟩` — **succeeds in 2 lines**, pure
mathlib.

Conclusion: **COMPOSABLE**. Both the concrete lemma (over its `Sum.elim` family) and the abstract
general fact are ≤3-call compositions of existing mathlib primitives (`weaken` + a `Finset.sup`
bound, plus `comp` with the 1-Lipschitz relabel). No new mathlib lemma is needed or possible:
the *statement* is welded to project-local definitions (`frontierCoverFamily`, `faceMap*`,
`expMapBasis`), so it cannot go to mathlib as written; and the *general* fact behind it is a
two-line composition that mathlib would inline, not ship.

## Verdict: `Chebotarev.exists_lipschitzWith_frontierCoverFamily`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the only mathematical content is "common Lipschitz constant =
  `max` of finitely many constants" — folklore/trivial; no named theorem; mathlib already has
  the abstract half (`LipschitzWith.max`, `LipschitzWith.uniformEquicontinuous`).
- Generality analysis (Phase 4): STRICTLY NARROWER, but the "general form" is itself the trivial
  composition, not a mathlib-worthy lemma; Phase 4c found no modernisation.
- Mathlib search (Phase 5): not in mathlib; **all building blocks present**
  (`LipschitzWith.weaken/.comp/.const`, `Finset.le_sup`, `le_sup_left`, `le_sup_of_le_right`).
- Composition check (Phase 6): COMPOSABLE — the proof body is already a ≤3-call-per-branch
  assembly; the general fact is a 2-line `choose … + Finset.univ.sup … + weaken`.
- Call sites (Phase 6.0): K = 0 external, exactly one in-file consumer
  (`normLeOne_frontier_lipschitz_cover`).

**Rationale:**

This theorem is **glue, not mathematics destined for mathlib**. Its statement is hard-wired to
`frontierCoverFamily K`, a project-local `Sum.elim` of three `expMapBasis`-based face maps
(`faceMapZero`, `faceMapSide`, const `0`) that live entirely inside the Chebotarev
`normLeOne`-frontier construction. A lemma whose *statement* names a project-local definition
cannot be upstreamed verbatim; mathlib would never carry "the cover family of the `normLeOne`
frontier has a uniform Lipschitz constant." Strip the concrete family and what remains is the
folklore fact "a finite family of Lipschitz maps shares the constant `sup Kₛ`" — which is a
two-line composition (`choose`, `Finset.univ.sup`, `LipschitzWith.weaken`) whose abstract half
(`LipschitzWith.max`, `LipschitzWith.uniformEquicontinuous`) mathlib already has. So neither the
concrete lemma (un-upstreamable) nor its abstraction (inline-able in ≤3 calls) is a mathlib
contribution.

Despite living in a `ForMathlib/` file and being author-earmarked, this particular helper is
correctly characterised as **internal scaffolding**: zero external call sites, one in-file
consumer, body = 6 lines of `weaken`/`comp`/`Finset.le_sup` bookkeeping. The earmark is best
read as targeting the *headline* of the file — `normLeOne_frontier_lipschitz_cover` and its
`mixedSpace`/`index` variants (the actual GRS §3.3 Lipschitz-boundary result) — not this
uniform-constant lemma, which is plumbing under that headline.

**WHY not (refactor-actionable):**

Mathlib has the building blocks; the result is a ≤3-call composition, so no new mathlib lemma is
justified. Two concrete options, both keeping it project-local:

Mathlib building blocks:
- `LipschitzWith.weaken` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:172`
- `LipschitzWith.comp` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:228`
- `LipschitzWith.const` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:197`
- `Finset.le_sup` — `Mathlib/Data/Finset/Lattice/Fold.lean:118`
- `le_sup_left`, `le_sup_of_le_right` — `Mathlib/Order/Lattice.lean:140,156`

Composition sketch (the general fact, ≤3 lines — for the abstract half, if ever wanted locally):
```lean
example {ι X Y : Type*} [Fintype ι] [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {g : ι → X → Y} (h : ∀ s, ∃ K : ℝ≥0, LipschitzWith K (g s)) :
    ∃ M : ℝ≥0, ∀ s, LipschitzWith M (g s) := by
  classical
  choose K hK using h
  exact ⟨Finset.univ.sup K, fun s ↦ (hK s).weaken (Finset.le_sup (Finset.mem_univ s))⟩
```

Call sites in our project (from Phase 6.0): K = 1 (the in-file `normLeOne_frontier_lipschitz_cover`
at line 354).

Refactor plan:
- **Recommended:** keep the lemma where it is, but mark it `private` (or leave as-is) — it is a
  legitimate local helper for `normLeOne_frontier_lipschitz_cover` in the same file, and
  factoring the three-branch `Sum.elim` Lipschitz bound out of that theorem aids readability.
  Do **not** ship it to mathlib. The file's genuine mathlib candidates are the public cover
  theorems (`normLeOne_frontier_lipschitz_cover` and its `mixedSpace`/`index` variants), which
  should be assessed separately.
- **Alternative (inline):** if the file is being slimmed, inline the 6-line proof into
  `normLeOne_frontier_lipschitz_cover`'s `obtain` at line 354, since it has exactly one consumer.
- If a reusable abstraction is ever wanted, it is the *general* `exists_lipschitzWith_of_forall`
  above (over `Fintype ι` + `PseudoEMetricSpace`), and **that** — not the `frontierCoverFamily`
  form — would be the only thing worth a mathlib look; but even it is a 2-line composition that
  mathlib review would most likely ask to be inlined rather than added.

Next action: do **not** PR `exists_lipschitzWith_frontierCoverFamily`. Keep it as a local helper
(optionally `private`) to `normLeOne_frontier_lipschitz_cover`, or inline it. Run `/mathlibable`
separately on the file's public cover theorems (`normLeOne_frontier_lipschitz_cover`,
`…_mixedSpace`, `…_index`) — those, not this plumbing lemma, are the upstreaming candidates.

---

## Next step

Do not PR this lemma. Keep `exists_lipschitzWith_frontierCoverFamily` project-local (mark
`private` or inline into its single consumer `normLeOne_frontier_lipschitz_cover`). It is a
≤3-call composition of mathlib's `LipschitzWith.weaken` / `.comp` / `.const` + `Finset.le_sup`
over a project-specific family, so no mathlib lemma is warranted. Assess the file's public cover
theorems separately.
