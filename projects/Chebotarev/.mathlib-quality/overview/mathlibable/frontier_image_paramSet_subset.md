# /mathlibable report — `Chebotarev.frontier_image_paramSet_subset`

## Baseline (Phase 0)
- lake build:               not run (local build stale per task note — reasoning from source, mathlib pin `d90090f647ca`)
- decl `Chebotarev.frontier_image_paramSet_subset`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:174`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` —
  covering the `realSpace` frontier `normAtAllPlaces '' (normLeOne K)` by finitely many
  Lipschitz images of the unit cube (Gun–Ramaré–Sivaraman / Widmer lattice-point boundary input).

Namespace: file opens `namespace Chebotarev` (verified — the parsed qualified name
`Chebotarev.frontier_image_paramSet_subset` is correct).

---

## Statement (Phase 1)

`Chebotarev.frontier_image_paramSet_subset` states: for a number field `K`, with
`expMapBasis : OpenPartialHomeomorph (realSpace K) (realSpace K)` mathlib's open injective
exponential-coordinate map (source `= univ`) and `paramSet K = Iic 0 ×ˢ [0,1)^{r-1}` (in the
`completeBasis` coordinates), the topological frontier of the image `expMapBasis '' (paramSet K)`
is contained in the image of the **box boundary** `closure (paramSet K) \ interior (paramSet K)`
together with the single escape point `{0}`:

> `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0}`.

The `{0}` accounts for closure points escaping to norm `0` as the unbounded `w₀`-coordinate
`→ -∞`. This is the **topological reduction** step that feeds the finite Lipschitz cover of the
frontier (the quantitative-regularity input to the effective lattice-point count).

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K]` — the number field.
- `expMapBasis K`, `paramSet K`, `compactSet K` — all **mathlib** objects from
  `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne` (imported at line 3).

Hypotheses (Lean side): none beyond the instances (it is an unconditional inclusion).

Conclusion (math): the boundary of the `expMapBasis`-image of the half-open box lies in the
image of the box's topological boundary, plus the origin.

Conclusion (Lean): `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0}`.

Proof (10 lines, for the composition analysis):
```
have hcl : closure (expMapBasis '' paramSet K) ⊆ compactSet K :=
  (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
    ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))
have hint : expMapBasis '' interior (paramSet K) ⊆ interior (expMapBasis '' paramSet K) :=
  (expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])).subset_interior_iff.mpr
    (Set.image_mono interior_subset)
refine (Set.diff_subset_diff hcl hint).trans ?_
rw [compactSet_eq_union, Set.union_diff_distrib, ← Set.image_diff (injective_expMapBasis K)]
exact Set.union_subset_union_right _ Set.diff_subset
```

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — the "topological reduction" step inside the file's Lipschitz-cover
pipeline; not itself a `## Main result`, not named after a person, introduces no structure.
(Literature width was EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def` — one-line check **n/a** (the body is a 10-line proof in any case).

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | frontier of image under open map subset image of frontier topology                                     | partial | `f⁻¹(∂Y) ⊆ ∂(f⁻¹X)` (preimage dir.) standard; image dir. folklore | nLab "open map", Wikipedia "Open and closed maps" — no *named* image-side theorem |
|  2 | WebSearch (general form)         | "frontier" image "open map" injective "closure" "interior" boundary preimage homeomorphism             | partial | "open maps: preimage of boundary ⊆ boundary"; "continuous bijection open ⇔ homeo" | image-side `∂(f A)` not isolated as a theorem |
|  3 | WebSearch (named-after / aliases)| boundary of image f(A) open embedding equals f(boundary A) intersect image                              | partial | embedding = homeo onto image (nLab "embedding of topological spaces) | the `∂(fA)=f(∂A)∩im` identity is folklore, unnamed |
|  4 | WebSearch (general theorem)      | "frontier(f(A))" / "boundary of the image" open map "f(∂A)" relationship general theorem               | partial | Hatcher/USTC notes + PlanetMath: `∂A = Ā \ int A`; open-map boundary result is **preimage** direction | Prop 3.6-style results are all preimage-side |
|  5 | ChatGPT MCP                      | cleanest general statement of frontier-of-image under open-injective map; named theorem or composition? | **DOWN** | Codex MCP failed twice (env note: MCP down) — fell back to WebSearch + manual analysis | recorded as attempted-but-unavailable |
|  6 | Local references                 | grep `.mathlib-quality/references/`                                                                     | n/a  | directory absent                  | no `references/` dir in this project (only `overview/`); recorded n/a |
|  7 | nLab                             | open map; embedding of topological spaces                                                               | yes  | open map preserves interiors of preimages; embedding = homeo onto image | gives the *ingredients*, not the packaged image-frontier inclusion |
|  8 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not a categorical concept          | point-set topology of a specific NT cone; no categorical content |
|  9 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept  | this is analytic/measure-geometry of the Minkowski cone |
| 10 | MathOverflow / Math.StackExchange| boundary of image under open embedding                                                                  | partial | folklore Q&A: `∂(f A) ∩ im f = f(∂A)` for open embeddings; standard exercise | confirms it is a routine consequence, not a citable theorem |
| 11 | recent arXiv (last 5 years)      | open embedding image frontier / stratification frontier condition                                       | partial | "frontier condition ⇔ decomposition map open" (arXiv 2407.17690) | tangential; confirms open-map↔frontier link but not our inclusion |

Protocol pass: WebSearch ran ≥3 queries at different generality levels (#1 specific, #2 general,
#3/#4 named/aliases) ✓; ChatGPT MCP attempted but **environment-down** (recorded, fell back) ✓;
local refs checked (absent → n/a) ✓; nLab checked ✓; Stacks/nCatLab n/a with reason ✓;
MO + arXiv checked ✓.

### Literature summary (Phase 3)

Concept identified as: **frontier (topological boundary) of the image of a set under an open
(injective) map / open embedding** — equivalently the image-direction companion of the standard
"open maps and boundaries" fact.

Sources agree on the standard form: **yes**, but the *named/standard* statement in the literature
is the **preimage direction** (`f⁻¹(frontier Y) ⊆ frontier (f⁻¹ Y)` for open `f`). The
**image-direction** statement for an open embedding is folklore: it is universally treated as a
routine exercise (Munkres/Willard-level), not a named theorem.

Most general standard form (image direction): for `f : X → Y` an **open map** and `s ⊆ X`,
`f '' (interior s) ⊆ interior (f '' s)`, hence
`frontier (f '' s) = closure (f '' s) \ interior (f '' s) ⊆ closure (f '' s) \ f '' (interior s)`;
and if additionally `f` is **continuous and injective** (an open embedding / `OpenPartialHomeomorph`
with `source = univ`), the sharp form is
`frontier (f '' s) ∩ range f ⊆ f '' (frontier s)`.

Generality dimensions where the literature varies:
- **the map**: open map → open *continuous injective* map (open embedding) → full homeomorphism.
  The full-homeomorphism case gives *equality* `frontier (f '' s) = f '' frontier s`; the
  open-embedding case gives the inclusion-on-the-range; the bare open-map case gives only the
  one-sided `⊆ closure (f''s) \ f''(int s)`.
- **the range**: when `range f` is the whole space (homeomorphism) there is no escape set; when
  `range f` is a *proper open subset* the frontier can pick up points of `(closure (f''s)) \ range f`
  — the abstract analogue of the project's `{0}`.

Disagreement with the literature: **none**. The project lemma is a *correct specialization*: it
takes `f = expMapBasis` (an open embedding with proper range), `s = paramSet K`, and replaces the
abstract escape set `closure (f''s) \ range f` by the concrete `{0}` via the mathlib-local fact
`compactSet K = expMapBasis '' closure (paramSet K) ∪ {0}` (`compactSet_eq_union`).

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): for an **open embedding** `f` (`IsOpenMap f` +
`Continuous f` + `Function.Injective f`, or `f : OpenPartialHomeomorph` with `source = univ`) and
any `s`, `frontier (f '' s) ⊆ f '' (closure s \ interior s) ∪ (closure (f '' s) \ range f)`; on the
range, `frontier (f '' s) ∩ range f ⊆ f '' frontier s`.

### Generality status table — `Chebotarev.frontier_image_paramSet_subset`

| # | Parameter / hypothesis           | Current Lean form                              | Literature-standard form                              | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------------|------------------------------------------------|--------------------------------------------------------|---------------------|----------------------------------|
| 1 | the map (`expMapBasis K`)        | one fixed mathlib `OpenPartialHomeomorph` (source `univ`) | **any** open embedding `f` / `OpenPartialHomeomorph` with `source = univ` | **yes** | proof uses only: `f` is an open map on its source (step `isOpen_image_of_subset_source`) and `f` is injective (step `image_diff` / `injective_expMapBasis`). Nothing about exp-coordinates is used. |
| 2 | the set (`paramSet K`)           | one fixed half-open box                         | **any** subset `s`                                     | **yes** | proof never inspects `paramSet`; `closure`/`interior`/`subset_closure`/`interior_subset` are generic. |
| 3 | the escape set (`{0}`)           | the literal singleton `{0}`                      | the abstract `closure (f '' s) \ range f`             | **yes** | `{0}` only arises because `compactSet_eq_union` computes `closure (expMapBasis '' closure(paramSet)) ∪ {0}`; the general bound is `closure (f''s) \ f''(closure s)`. |
| 4 | the closed-set bound (`compactSet K`) | the specific mathlib `compactSet`           | `closure (f '' s)` itself                              | **yes** | `hcl` proves `closure (f''s) ⊆ compactSet`; in the general statement one just uses `closure (f''s)` directly and never needs a named compact superset. |
| 5 | `[NumberField K]`, `[Field K]`   | number-field instances                          | none (pure topology)                                  | **yes** | the general statement is in `[TopologicalSpace X] [TopologicalSpace Y]` with no algebra. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: 5 (every parameter is a specialization of a pure-topology
general form).

Proposed restatement (the literature-standard general lemma — the real mathlib target):
```lean
-- General topology, no number theory.
theorem IsOpenMap.frontier_image_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsOpenMap f) (s : Set X) :
    frontier (f '' s) ⊆ closure (f '' s) \ f '' interior s := by
  exact Set.diff_subset_diff_right (hf.image_interior_subset s) -- (frontier ⊆ closure \ interior)

-- Sharp open-embedding form (gives the project lemma after the {0} closure-computation):
theorem IsOpenEmbedding.frontier_image_subset            -- or on OpenPartialHomeomorph, source = univ
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsOpenEmbedding f) (s : Set X) :
    frontier (f '' s) ⊆ f '' (closure s \ interior s) ∪ (closure (f '' s) \ range f) := by
  sorry  -- closure(f''s) \ f''(int s) ⊆ f''(closure s \ int s) ∪ (closure(f''s) \ range f),
         -- via Set.image_diff hf.injective and a range split. Proof should survive.
```
The project lemma is then `(IsOpenEmbedding.frontier_image_subset …)` with the abstract escape
set rewritten to `{0}` by `compactSet_eq_union`/`expMapBasis_closure_subset_compactSet`.

Cost of restatement: **CHEAP–MODERATE**. The bare-open-map form (`IsOpenMap.frontier_image_subset`)
is a 1-line mechanical rewrite. The sharp open-embedding form needs the `Set.image_diff`-on-the-
range step (already present in the current proof) — a short, idea-free adaptation.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                               | no       | already typeclass-based | — |
|  2 | sequences/metric → filters/topological?                                                           | no       | already purely topological (closure/interior/frontier) | — |
|  3 | construct an object → universal-property class?                                                   | no       | it is a `⊆` fact, no construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                | no       | the sets are genuine ad-hoc subsets, not substructures | — |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                                          | **yes**  | drop `[NumberField K]`/`[Field K]`; state over `[TopologicalSpace X] [TopologicalSpace Y]` (see 4b) | the entire `IsOpenMap`/`IsOpenEmbedding`/`OpenPartialHomeomorph` image-frontier API; reusable in measure theory, manifolds, complex analysis |
|  6 | 1-categorical → higher-categorical?                                                               | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure?                                           | no       | no numeric index present | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it coincides with the Phase-4b generalisation rather than
adding a *new* idiom. The right mathlib object is the **general `IsOpenMap`/`IsOpenEmbedding`
image-frontier lemma** sitting in `Mathlib/Topology/Maps/Basic.lean`, alongside the existing
`IsOpenMap.preimage_frontier_subset_frontier_preimage`. That is a real organisational improvement:
mathlib currently has the *preimage*-direction open-map frontier lemma and the *equality* for full
homeomorphisms (`Homeomorph.image_frontier`), but **no image-direction lemma for open maps /
open embeddings** — a visible asymmetry in the API.
  - Real mathematical improvement: closes the image-vs-preimage asymmetry in mathlib's open-map
    frontier API; the general lemma then specializes to *this* result and to any future
    "boundary of an embedded set" need (measure theory, submanifolds, holomorphic charts).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.frontier_image_paramSet_subset`

[A] Lean-Finder       (MCP unavailable here)                                         n/a: index tool not wired in this env
[B] Loogle            `frontier (?f '' ?s) ⊆ _` ; `IsOpenMap → frontier`            no hits (image direction); see grep [D]
[C] LeanSearch        (MCP unavailable here)                                         n/a: index tool not wired in this env
[D] Grep mathlib src  `frontier.*''`, `IsOpenMap.*frontier`, `image_frontier`,      see results below
                      `IsOpenEmbedding.*frontier`, `frontier_image`
[E] Name pattern      `frontier_image_paramSet_subset`, `compactSet`, NormLeOne     resolved (project decl; mathlib stops at the *measure* result)

Grep [D] results (mathlib pin d90090f, `Mathlib/Topology/`):
- `IsOpenMap.preimage_frontier_subset_frontier_preimage` (Maps/Basic.lean:449) — **preimage** direction.
- `IsOpenMap.preimage_frontier_eq_frontier_preimage` (Maps/Basic.lean:455) — **preimage** direction.
- `Homeomorph.image_frontier` (Homeomorph/Defs.lean:312) — `h '' frontier s = frontier (h '' s)`,
  but **only for a full homeomorphism** `h : X ≃ₜ Y` (range = univ; no escape set possible).
- `OpenPartialHomeomorph.IsImage.preimage_frontier` (IsImage.lean:201) — **preimage**, source-restricted.
- **No** `IsOpenMap`/`IsOpenEmbedding`/`OpenPartialHomeomorph` lemma bounding `frontier (f '' s)`
  in the image direction (`grep IsOpenMap … frontier | grep -v preimage` → empty;
  `IsOpenEmbedding … frontier` → empty).

Mathlib's `NormLeOne` endpoint (the file this lemma specializes):
- `compactSet_eq_union` (NormLeOne.lean:779), `expMapBasis_closure_subset_compactSet` (:789),
  `isCompact_compactSet` (:725), `injective_expMapBasis` (:474),
  `OpenPartialHomeomorph.isOpen_image_of_subset_source`, `expMapBasis_source` (:470) — **all present**
  (these are exactly the lemma's inputs).
- The boundary result mathlib *does* prove is the **measure-zero** statement
  `volume_frontier_normLeOne : volume (frontier (normLeOne K)) = 0` (NormLeOne.lean:868) and
  `compactSet_ae`/`volume_interior_eq_volume_closure` — i.e. mathlib stops at the a.e./measure
  level and never states the **pointwise** frontier-inclusion the project needs.

Searched for both:
  - the user's current form (`expMapBasis`/`paramSet`/`{0}`) — **not in mathlib** (mathlib has the
    measure-zero result, not this pointwise inclusion).
  - the literature-standard general form (open-map / open-embedding image-frontier) — **not in
    mathlib** (only preimage-direction + full-homeomorphism equality exist).

Concluded: **not in mathlib** (neither the `expMapBasis`-specific pointwise inclusion nor the
general image-direction open-map/open-embedding frontier lemma exists; the building blocks —
`IsOpenMap.image_interior_subset`, `frontier_eq_closure_diff_interior`, `Set.image_diff`,
`compactSet_eq_union` — are all present).

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `Chebotarev.frontier_image_paramSet_subset`

Internal use count: **1** (within the project, excluding the declaring line)
External-to-file callers: 0 distinct files (the one use is in the *same* file)

| Caller file:line                                              | Usage pattern (one-line excerpt)                               |
|--------------------------------------------------------------|----------------------------------------------------------------|
| ForMathlib/NormLeOneLipschitz.lean:319                       | `refine (frontier_image_paramSet_subset K).trans (Set.union_subset …)` |

(Lines 45 and 310 are docstring mentions, not uses.) The single use is the first link of the
`frontier_subset_frontierCoverFamily` chain (frontier → box-boundary image ∪ {0} → face images).

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?): **none** —
no other site reconstructs `frontier (expMapBasis '' …) ⊆ …`.

Call-sites reading: K = 1 internal use, no external consumers, no inline re-derivation. By the
Phase-6 signal table this is "K = 1 → possibly the wrong abstraction; could be inlined" — but here
it is a *named intermediate* in a published-API pipeline, so the K = 1 count reflects that it is a
one-shot reduction step, not dead code. It does **not** by itself argue for mathlib inclusion of
the *specialized* form; it argues for the *general* form (which would have many more potential
consumers) — consistent with the Phase-4 verdict.

### Composition check (Phase 6)

Can `Chebotarev.frontier_image_paramSet_subset` be derived from mathlib in ≤3 chained calls?

Attempt 1: `(IsOpenMap.image_interior_subset … ).trans …`
  - Mathlib decls used: `IsOpenMap.image_interior_subset`, `frontier_eq_closure_diff_interior`.
  - Result: **partial** — gives the bare-open-map bound `frontier (f''s) ⊆ closure (f''s) \ f''(int s)`,
    but NOT the project's RHS (`f '' (closure s \ int s) ∪ {0}`). To finish you must additionally
    (i) bound `closure (f''s)` by `compactSet` (`expMapBasis_closure_subset_compactSet` + a
    `closure_subset_iff`), (ii) rewrite `compactSet` by `compactSet_eq_union`, (iii) distribute the
    set-difference over the union (`Set.union_diff_distrib`), and (iv) pull it through the image with
    injectivity (`Set.image_diff (injective_expMapBasis K)`). That is **4+ further mathlib calls with
    genuine set-algebra glue**, i.e. the actual 10-line proof.

Attempt 2: `Homeomorph.image_frontier`
  - Result: **fails** — requires a *full* homeomorphism (range = univ). `expMapBasis` is only an
    `OpenPartialHomeomorph` with proper range, so the escape point `{0}` genuinely appears and the
    clean equality is unavailable.

Conclusion: **NOT-COMPOSABLE** in ≤3 calls. The proof is a real (short) argument that splices two
mathlib-`NormLeOne` lemmas (`compactSet_eq_union`, `expMapBasis_closure_subset_compactSet`) with
generic topology + set-algebra; it is not a `.trans`/`.symm`/single-application composition.

---

## Verdict: `Chebotarev.frontier_image_paramSet_subset`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): the underlying fact (boundary of an embedded set under an open
  embedding) is standard *folklore*; the **named** standard theorem is the preimage direction;
  the image-direction inclusion is universally treated as a routine consequence at the level of
  `IsOpenMap.image_interior_subset` + `frontier = closure \ interior` + `Set.image_diff`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — all 5 parameters
  (`expMapBasis`, `paramSet`, `{0}`, `compactSet`, the `NumberField` instances) are specializations
  of a pure-topology general form; the modern-idiom check confirms the proper target is a general
  `IsOpenMap`/`IsOpenEmbedding` image-frontier lemma in `Mathlib/Topology/Maps/Basic.lean`.
- Mathlib search (Phase 5): **not in mathlib** in either form — mathlib has the *preimage*-direction
  open-map frontier lemmas and the *full-homeomorphism* equality `Homeomorph.image_frontier`, but no
  image-direction open-map/open-embedding lemma; and on the NT side mathlib stops at the *measure*
  result `volume_frontier_normLeOne`, never the pointwise inclusion.
- Composition check (Phase 6): **NOT-COMPOSABLE** in ≤3 calls (10-line proof gluing two
  `NormLeOne` lemmas with set-algebra; `Homeomorph.image_frontier` is inapplicable because the
  range is proper).

**Rationale:**

The result is genuinely missing from mathlib, so this is not a NO verdict — but the *form* the
author wrote is a number-field specialization of a pure point-set-topology fact, so it is not
`YES-add-as-is` either. The proof uses nothing about exponential coordinates: it uses (1) that
`expMapBasis` is an **open map on its source** and (2) that it is **injective**, plus the
mathlib-local closure computation `compactSet_eq_union` to name the escape set as `{0}`. Strip those
two facts out and the statement is the literature-standard image-direction frontier inclusion for an
open embedding — which mathlib conspicuously lacks even though it has the *preimage* companion
(`IsOpenMap.preimage_frontier_subset_frontier_preimage`) and the *full-homeomorphism* equality
(`Homeomorph.image_frontier`). The right mathlib contribution is therefore the **general lemma**,
after which `frontier_image_paramSet_subset` becomes a thin specialization (general lemma + a rewrite
by `compactSet_eq_union`) that belongs next to mathlib's own `NormLeOne` `compactSet` API — the very
file it already specializes — or is inlined there.

Because Phase 4b is STRICTLY NARROWER, the verdict gate forbids `YES-add-as-is`; because the result
is absent from mathlib, it is not a NO bucket; the generalisation is CHEAP–MODERATE (the current
proof's `Set.image_diff` step already does the only non-mechanical work), so it is not a
cost-driven BORDERLINE. Hence **YES-but-generalise-first**.

  Reason for the generalisation:
    - LITERATURE-WEAKENING: Phase 4b found the user's form strictly narrower than the
      literature-standard (pure-topology) form — drop `expMapBasis`/`paramSet`/`{0}`/`compactSet`/
      `NumberField` for an arbitrary open embedding `f` and arbitrary `s`.
    - MODERN-IDIOM (Bourbaki 2.0): the general lemma closes the image-vs-preimage asymmetry in
      mathlib's open-map frontier API.
  Proposed restatement:
  ```lean
  -- in Mathlib/Topology/Maps/Basic.lean, beside preimage_frontier_subset_frontier_preimage:
  theorem IsOpenMap.frontier_image_subset
      {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
      (hf : IsOpenMap f) (s : Set X) :
      frontier (f '' s) ⊆ closure (f '' s) \ f '' interior s :=
    Set.diff_subset_diff_right (hf.image_interior_subset s)

  -- open-embedding refinement that yields the project lemma after the {0} computation:
  theorem IsOpenEmbedding.frontier_image_subset
      {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
      (hf : IsOpenEmbedding f) (s : Set X) :
      frontier (f '' s) ⊆ f '' (closure s \ interior s) ∪ (closure (f '' s) \ Set.range f) := by
    sorry -- from frontier ⊆ closure(f''s) \ f''(int s), split on range f, Set.image_diff hf.injective
  ```
  Estimated cost of regeneralisation: **CHEAP–MODERATE** (the bare-open-map form is one line; the
  open-embedding form reuses the existing `Set.image_diff` step — proof should survive).
  Mathlib downstream this enables:
    - the symmetric image-direction partner to `IsOpenMap.preimage_frontier_*`;
    - immediate specialization to `Chebotarev.frontier_image_paramSet_subset` (general lemma +
      `compactSet_eq_union` rewrite), removing all bespoke set-algebra from the project;
    - reuse anywhere an embedded set's boundary is needed (measure theory of images, submanifold
      boundaries, holomorphic charts) — the old NT-specific form blocked all of that.
  Next action: run `/generalise Chebotarev.frontier_image_paramSet_subset` to extract the general
  `IsOpenMap.frontier_image_subset` (+ `IsOpenEmbedding` refinement) tensioned against both the
  literature image-direction form and the existing `IsOpenMap.preimage_frontier_*` mathlib API,
  then PR the general lemma to `Mathlib/Topology/Maps/Basic.lean`; keep the `expMapBasis`
  specialization project-local (or upstream it to mathlib's `NormLeOne` file as a one-line corollary).

---

## Next step

Run `/generalise Chebotarev.frontier_image_paramSet_subset`: extract the pure-topology
`IsOpenMap.frontier_image_subset` (and the `IsOpenEmbedding`/`OpenPartialHomeomorph` refinement that
carries the escape set), PR it to `Mathlib/Topology/Maps/Basic.lean` next to
`IsOpenMap.preimage_frontier_subset_frontier_preimage`, and reduce the project lemma to a one-line
specialization.
