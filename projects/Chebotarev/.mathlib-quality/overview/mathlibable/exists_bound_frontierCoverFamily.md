# /mathlibable report — `Chebotarev.exists_bound_frontierCoverFamily`

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build is stale per task brief; reasoning from source statement, as instructed)
- decl `Chebotarev.exists_bound_frontierCoverFamily`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:530`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the
  effective-lattice-point input (Gun–Ramaré–Sivaraman §3.3 / Widmer–Lang GTM 110) saying the
  frontier of `normAtAllPlaces '' normLeOne K` is covered by finitely many Lipschitz images of `[0,1]^{r-1}`.

The file lives under `ForMathlib/`, author-earmarked for mathlib, but each decl is assessed on its own merits.

---

### Statement (Phase 1)

`Chebotarev.exists_bound_frontierCoverFamily` is a **theorem** stating:

> The finite family `frontierCoverFamily K` of cube-parametrisation maps is **uniformly bounded**:
> there is a single constant `B : ℝ` such that for every face index `s` and every point `c` of the
> coordinate space, `‖frontierCoverFamily K s c‖ ≤ B`.

`frontierCoverFamily K` (defined line 284) is `Sum.elim`-assembled over the finite index type
`Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)`:
- the `inl` branch is the constant `0` map (the `{0}` closure point),
- the two right branches are `faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K` and
  `faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K`.

The face maps `faceMapZero`/`faceMapSide` are restrictions of globally `C¹` maps (`expMapBasis`,
which is `ContDiff ℝ 1`); the key is that each is post-composed with `clampUnit`, the
coordinatewise retraction of `ℝ^n` onto the unit cube `Icc 0 1` (so `c` may range over the *whole*
space yet the face map only ever sees a point of the **compact** cube).

Variables / typeclasses (Lean side):
- `K` : a number field (`[Field K] [NumberField K]`, fixed throughout the file's `Chebotarev` namespace).
- codomain `realSpace K = InfinitePlace K → ℝ` — a finite-dimensional sup-normed pi-type.

Hypotheses (Lean side): none beyond the ambient `K`; the boundedness is unconditional because the
family is finite and each member is continuous-on-a-compact-image.

Conclusion (math): the finite family of cube-face maps has a common sup-norm bound `B`.
Conclusion (Lean): `∃ B : ℝ, ∀ s c, ‖frontierCoverFamily K s c‖ ≤ B`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma about the project-specific family `frontierCoverFamily`; not a new structure,
not named after a person, not a `## Main results` entry. (The `## Main results` are
`normLeOne_frontier_lipschitz_cover{,_mixedSpace,_index}`; this lemma is internal scaffolding —
the boundedness hypothesis `hB` feeding `lipschitzWith_liftToMixed`.)

(Literature width run EXHAUSTIVE regardless, per the skill.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` — one-line check **n/a**. (Body is a ~20-line
`by` proof: per-face compact-image boundedness + a finite `Finset.sup` merge + NNReal coercion plumbing.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "continuous function on compact set is bounded uniform bound finite family mathlib"                     | yes  | boundedness theorem; `f` cont. on compact `K` ⟹ `∃ M, |f| ≤ M` | LibreTexts, mathlib4 docs (`Topology.Compactness.Compact`, `ContinuousMap.Bounded.Basic`) |
|  2 | WebSearch (general form)         | "continuous image of compact set is bounded standard theorem extreme value"                            | yes  | continuous image of compact is **compact** ⟹ closed + bounded (Heine–Borel) | Wolfram MathWorld, Wikipedia EVT, jmeiners lecture notes |
|  3 | WebSearch (named-after / aliases)| "boundedness theorem continuous function compact extreme value theorem corollary bounded"               | yes  | "**Boundedness Theorem**", a corollary of the **Extreme Value Theorem** (Weierstrass) | GMU 315, S.Carolina Math554 handouts, technologyuk |
|  4 | ChatGPT MCP                      | standard name + generality of "cont. on compact ⟹ bounded"; is the FINITE-family uniform-bound version named? | n/a  | (MCP down — Codex exec failed; fallback = WebSearch + source analysis, per task brief) | recorded n/a with reason; channels 1–3 + 6 + 9 already answer the standard-form + naming question |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "bound"/"compact"                                              | n/a  | (no references dir for Chebotarev — `projects/Chebotarev/.mathlib-quality/references/` absent) | recorded n/a |
|  6 | nLab                             | "extreme value theorem continuous map compact image bounded"                                            | yes  | EVT = special case of "continuous images of compact spaces are compact"; image bounded by Heine–Borel | ncatlab.org/nlab/show/extreme+value+theorem; …/continuous+images+of+compact+spaces+are+compact |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept (point-set boundedness fact) | recorded n/a |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | not an algebraic-geometry concept | recorded n/a |
|  9 | MathOverflow / Math.SE           | (covered transitively via ProofWiki "Extreme Value Theorem" + lecture-note hits in #1–#3)              | yes  | confirms "Boundedness Theorem" is the corollary name; finite-family version regarded as trivial max | ProofWiki Extreme_Value_Theorem |
| 10 | recent arXiv (last 5 years)      | (1807.08416 "Some Fundamental Theorems in Mathematics", 0709.4492 "Fun with Analysis I")               | yes  | EVT/boundedness treated as a *fundamental, century-old* theorem — no modern reformulation of the finite-family corollary | confirms nothing new here |

The protocol passed: WebSearch ran 3 distinct generality-level queries; nLab checked; Stacks/nCatLab
recorded n/a with reason; MathOverflow/arXiv covered. ChatGPT MCP recorded n/a (server down per the
task brief) — the standard-form and naming questions are nonetheless fully answered by the other channels.

### Literature summary (Phase 3)

Concept identified as: the **Boundedness Theorem** — a continuous function on a compact set is bounded
— itself the bounded half of the **Extreme Value Theorem** (Weierstrass), and the metric-space shadow
of "the continuous image of a compact set is compact".

Sources agree on the standard form: **yes**. Most general standard form: a continuous map from a
compact space into a (pseudo)metric / normed space has bounded image (`f(K)` is compact, hence bounded).

Generality dimensions where the literature varies:
  - domain: closed interval `[0,1]` (calculus texts) → arbitrary compact set/space (topology texts). Most general: compact space.
  - codomain: ℝ (EVT, with attained max/min) → any (pseudo)metric / normed target (boundedness only). Most general for *boundedness*: pseudometric space.

**The finite-family uniform-bound version** ("finitely many continuous-on-compact maps ⟹ one common
bound") is **universally regarded as a trivial corollary**: take the maximum of the finitely many
per-map bounds. No source gives it a name of its own. This is the exact shape of the user's lemma
(`∃ B, ∀ s c, …`, `s` over a finite index, each member continuous on the compact cube image).

Disagreement with the literature: none.

---

### Generality analysis — `Chebotarev.exists_bound_frontierCoverFamily` (Phase 4)

Literature-standard form (from Phase 3): "continuous map on a compact set ⟹ bounded image"
(boundedness theorem); the finite-family version is the trivial finite-max corollary.

| # | Parameter / hypothesis        | Current Lean form                                  | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | the family `frontierCoverFamily K` | a *specific* finite family of cube-face maps tied to `expMapBasis` / `paramSet` of a number field | "a finite family of continuous maps each bounded on a compact set" | yes (in principle) | The general statement is the project-agnostic "finite family of compact-image continuous maps is uniformly bounded" — but that general statement **is exactly what mathlib already composes** (`IsCompact.exists_bound_of_continuousOn` + finite `sup`); abstracting `frontierCoverFamily` out of the statement just *recovers* the mathlib building block. There is no intermediate "right generality" between the bespoke instance and the mathlib primitive. |
| 2 | codomain `realSpace K` (sup-normed pi-type) | concrete `InfinitePlace K → ℝ` | any normed/(pseudo)metric space | yes | the proof uses only `IsCompact.image`, `IsBounded`, `subset_closedBall` — all available for any pseudometric codomain; but this weakening only matters for a *general* lemma, which is the mathlib primitive, not a `frontierCoverFamily` statement. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in the degenerate way that makes
generalisation collapse onto an existing mathlib primitive rather than onto a new contributable lemma.
The maximally-general statement of "this" is *literally* `IsCompact.exists_bound_of_continuousOn`
(per member) merged by `Bornology.isBounded_iUnion` / a finite `Finset.sup`. There is **no
project-agnostic restatement that is both (a) more general than the bespoke instance and (b) not
already in mathlib**. So this is not a "generalise-first then PR" case; it is a "the general thing
already exists, this is a bespoke application" case.

Number of weakening opportunities found: 0 *that land on a new mathlib-worthy lemma* (every
weakening recovers an existing mathlib primitive).
Proposed restatement: none worth PR'ing — see Phase 5/6.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                            | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                            | no       | already typeclass-driven (`NumberField K`); the family is a plain `def` | — |
|  2 | sequences/metric → filters/topological?                                                              | no       | boundedness is already stated via `IsBounded`/bornology; no sequence to filter-ise | — |
|  3 | construct an object → universal-property class?                                                      | no       | this is an existence-of-bound statement, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                   | no       | no substructure here | — |
|  5 | vector-space/metric/field-specific → weaken via typeclass hierarchy?                                 | no (n/a) | the *general* fact is already maximally weak in mathlib (`IsCompact.exists_bound_of_continuousOn`); the user's lemma is a fixed-`K` instance, nothing to re-typeclass | — |
|  6 | 1-categorical → higher-categorical?                                                                  | no       | not categorical | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid?                                            | no       | the index `s` is an abstract finite sum type already; `c`'s domain is the cube coordinate space, not a numeric index to generalise | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is a finitary existence-of-uniform-bound fact about a
specific number-field cube family; there is no contemporary-mathlib reformulation that improves its
mathematical organisation. The "modern" form of the underlying *general* fact already exists in
mathlib as `IsCompact.exists_bound_of_continuousOn`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `Chebotarev.exists_bound_frontierCoverFamily` (Phase 5)

[A] Lean-Finder       n/a: AI-search UI not reachable from this environment (build stale). Compensated by exhaustive grep (method D).
[B] Loogle            `IsCompact _ → ContinuousOn _ _ → ∃ _, ∀ _, ‖_‖ ≤ _`  — tool unavailable in this env (deferred `lean_loogle` not surfaced). Compensated by D/E.
[C] LeanSearch        "continuous function on compact set bounded" / "uniform bound finite family of continuous maps" — tool unavailable (deferred not surfaced). Compensated by web (Phase 3 #1) which returned the mathlib docs pages.
[D] Grep mathlib src  `exists_bound`, `IsCompact.*isBounded`, `IsCompact.*image`, `subset_closedBall`, `isBounded_iUnion`, `isBounded_biUnion`, `Finite.isBounded` over `.lake/packages/mathlib/` — **HITS** (see below)
[E] Name pattern      `IsCompact.exists_bound_of_continuousOn`, `exists_norm_le`, `exists_pos_norm_le` — **HITS**

**Building blocks found in mathlib (method D/E):**
- `IsCompact.exists_bound_of_continuousOn` — `Mathlib/Analysis/Normed/Group/Bounded.lean:96`
  (the `to_additive` of `IsCompact.exists_bound_of_continuousOn'`, lines 96–100):
  `(hs : IsCompact s) (hf : ContinuousOn f s) : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C`.
  **This is the per-face boundedness theorem, verbatim.**
- `IsCompact.isBounded` — `Mathlib/Topology/MetricSpace/Bounded.lean:192` ("A compact set is bounded").
- `IsCompact.image` / `IsCompact.image_of_continuousOn` — continuous image of compact is compact.
- `Bornology.IsBounded.subset_closedBall` — `Mathlib/Topology/MetricSpace/Bounded.lean:101`.
- `Bornology.isBounded_iUnion [Finite ι]` — `Mathlib/Topology/Bornology/Basic.lean:238`:
  `IsBounded (⋃ i, s i) ↔ ∀ i, IsBounded (s i)` (the finite-family merge, the abstract form of the `Finset.sup`).
- `isBounded_biUnion` / `Set.Finite.isBounded` — same file, the finitary aggregation primitives.

The **actual proof body** (lines 533–551) already uses exactly these: `isCompact_Icc.image hg`,
`.isBounded.subset_closedBall 0`, then `Finset.univ.sup`/`Finset.le_sup`/`le_sup_left` to merge the
finitely many per-face bounds — i.e. a hand-rolled `IsCompact.exists_bound_of_continuousOn` per face
plus a manual finite-sup aggregation.

Searched for both:
  - the user's current form (`∃ B, ∀ s c, ‖frontierCoverFamily K s c‖ ≤ B`) — **not in mathlib** (it
    is about a project-specific family; could not be, by construction).
  - the literature-standard form ("continuous-on-compact ⟹ bounded", and its finite-family corollary)
    — **the per-member form IS in mathlib** as `IsCompact.exists_bound_of_continuousOn`; the
    finite-family merge IS in mathlib as `isBounded_iUnion` / `Finset.sup`.

Concluded: **"found building blocks (`IsCompact.exists_bound_of_continuousOn`, `isBounded_iUnion`/
`Finset.sup` over `Finset.univ`); composition would yield our form."** The *named general theorem*
is `IsCompact.exists_bound_of_continuousOn`; the user's lemma is its finite-`Finset.sup` instantiation
on the `frontierCoverFamily` faces.

---

### Call sites — `Chebotarev.exists_bound_frontierCoverFamily` (Phase 6.0)

Internal use count: **0** outside the declaring file. (Repo-wide grep for the name returns only the
declaration at line 530 and **one** use at line 632, both inside
`ForMathlib/NormLeOneLipschitz.lean`.)

External-to-file callers: **0 distinct files**.

| Caller file:line                                          | Usage pattern (one-line excerpt)                                  |
|-----------------------------------------------------------|--------------------------------------------------------------------|
| ForMathlib/NormLeOneLipschitz.lean:632 (same file)        | `obtain ⟨B, hB⟩ := exists_bound_frontierCoverFamily K` — feeds `lipschitzWith_liftToMixed` inside `normLeOne_frontier_lipschitz_cover_mixedSpace` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?): **(none)** —
the per-face compact-image boundedness pattern (`IsCompact.image … |>.isBounded`) appears only inside
this lemma's own proof; no sibling re-derivation found in the project.

**Signal:** exactly **one** in-file consumer, **zero** external; no inline re-derivation. Per the
Phase-6 call-sites table this is the "K = 1 internal use only → possibly the wrong abstraction, could
be inlined" signal. It is genuine scaffolding for `normLeOne_frontier_lipschitz_cover_mixedSpace`,
not dead code — but it is single-use, in-file, and bespoke.

---

### Composition check (Phase 6)

Can `Chebotarev.exists_bound_frontierCoverFamily` be derived from mathlib in ≤3 chained calls?

Attempt 1 — per-member `IsCompact.exists_bound_of_continuousOn` + finite merge:
  - For each face `s`, `frontierCoverFamily K s = g_s ∘ clampUnit _ ∘ cubeRelabel K` with `g_s`
    continuous; its range ⊆ `g_s '' Icc 0 1` (compact image), so
    `IsCompact.exists_bound_of_continuousOn` gives a per-face `B_s`. Then `B := ⊔_s B_s` over the
    finite index (`Finset.univ.sup`) bounds them all.
  - Mathlib decls used: `IsCompact.exists_bound_of_continuousOn`, `isCompact_Icc`/`IsCompact.image`,
    `Finset.sup` + `Finset.le_sup` (or `Bornology.isBounded_iUnion`).
  - Result: **succeeds mathematically**, but it is **not a ≤3-call one-liner**: it requires a
    `rcases`/`Sum.elim` case split over the 3-branch index type, a `choose` over the `Bool`-indexed
    side faces, the `clampUnit`-lands-in-`Icc` step (`clampUnit_mem_Icc`, a *project* lemma), and
    NNReal-coercion plumbing for the `sup`. That is ~15–20 lines — a real proof, not a composition.
  - Notes: the `clampUnit`/`cubeRelabel` factoring and the per-branch handling are project-specific;
    the only *mathlib* content is the boundedness-theorem call per face.

Conclusion: **NOT-COMPOSABLE** as a ≤3-call inline (the merge + case-split + project-lemma glue is a
real proof). **However**, the lemma is not mathlib-worthy for the orthogonal reason that its
*statement* is about the project family `frontierCoverFamily` — there is no general statement here to
contribute; the general statement is `IsCompact.exists_bound_of_continuousOn`, which mathlib already has.

---

## Verdict: `Chebotarev.exists_bound_frontierCoverFamily`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the result is the **Boundedness Theorem** (bounded half of the Extreme
  Value Theorem); the finite-family uniform-bound version is the unnamed trivial finite-max corollary.
- Generality analysis (Phase 4): STRICTLY NARROWER, but every generalisation collapses onto an existing
  mathlib primitive — there is no new mathlib-worthy general form. Modern-idiom: none.
- Mathlib search (Phase 5): the general theorem **is in mathlib** as
  `IsCompact.exists_bound_of_continuousOn` (`Mathlib/Analysis/Normed/Group/Bounded.lean:96`); the
  finite merge is `Bornology.isBounded_iUnion` / `Finset.sup`.
- Composition check (Phase 6): the *user's bespoke statement* is a ~20-line proof (not a ≤3-call
  inline), so strictly it is not "NO-composable" in the inline-at-call-site sense — but it is also not
  a contribution, because mathlib already owns the general theorem it instantiates.

**Rationale (1–2 paragraphs):**

`exists_bound_frontierCoverFamily` is not a general mathematical statement — it asserts uniform
boundedness of the *specific* project family `frontierCoverFamily K`, a bespoke 3-branch family of
cube-face parametrisations built from `expMapBasis`/`paramSet` of a fixed number field. The
mathematical content it relies on is entirely classical and entirely present in mathlib: each face map
is continuous and (thanks to the `clampUnit` retraction onto `Icc 0 1`) is only ever evaluated on a
**compact** set, so by the **Boundedness Theorem** — mathlib's
`IsCompact.exists_bound_of_continuousOn` — its range is norm-bounded; a finite `Finset.sup` over the
finitely many faces (mathlib's `isBounded_iUnion` / `Finset.sup`) merges these into one constant `B`.
The literature search confirms (Wikipedia, nLab, ProofWiki, multiple analysis lecture notes) that this
is a century-old fundamental theorem with no modern reformulation, and that the finite-family version
is the *unnamed* "take the max of finitely many bounds" corollary.

The verdict is **NO-mathlib-has-it**: the *general* theorem this lemma instantiates already lives in
mathlib as `IsCompact.exists_bound_of_continuousOn`, and the only thing wrapping it here is
project-specific bookkeeping (`frontierCoverFamily`, `clampUnit`, `cubeRelabel`, the 3-way `Sum.elim`
case split, NNReal plumbing). It cannot itself go to mathlib (its statement names a project object),
and it should not be a standalone lemma anywhere beyond this file: it is single-use (exactly one
in-file consumer, `normLeOne_frontier_lipschitz_cover_mixedSpace`, line 632; zero external callers).
It is correctly placed as a `private`-flavoured local helper. (NB: this is a *boundary* between
NO-mathlib-has-it and NO-composable-from-mathlib — picked NO-mathlib-has-it because the decisive fact
is that the *general theorem* is owned by mathlib and the local lemma is a bespoke instantiation of it,
not because the 20-line bespoke proof inlines in ≤3 calls. The actionable consequence is the same:
keep it local, do not PR it, and ensure its proof leans on `IsCompact.exists_bound_of_continuousOn`.)

**WHY not (refactor-actionable detail):**
Mathlib already has the load-bearing general theorem. The specific named gap:
- **`IsCompact.exists_bound_of_continuousOn`** — `Mathlib/Analysis/Normed/Group/Bounded.lean:96`:
  `(hs : IsCompact s) (hf : ContinuousOn f s) : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C`. This is the per-face
  boundedness theorem verbatim.
- **`Bornology.isBounded_iUnion [Finite ι]`** — `Mathlib/Topology/Bornology/Basic.lean:238`, or the
  `Finset.sup` the current proof already uses, for the finite-family merge.

Existing mathlib decl:        `IsCompact.exists_bound_of_continuousOn`
Located at:                   `Mathlib/Analysis/Normed/Group/Bounded.lean:96`

Our form does **not** follow in ≤1 line (it is a finite-family/case-split wrapper), so a strict
`example : <our statement> := <one mathlib call>` is not available — which is exactly why the lemma is
*kept locally* rather than deleted-and-replaced. The refactor action is therefore **not** "delete and
re-call at K sites" (there is only the 1 in-file site, and no 1-line replacement exists); it is:

Refactor plan:
1. **Keep `exists_bound_frontierCoverFamily` local to the file** — do **not** include it in any
   `ForMathlib`→mathlib PR. Its statement is about `frontierCoverFamily K`, which is not a mathlib object.
2. **Optionally tighten the proof** to call `IsCompact.exists_bound_of_continuousOn` per face instead
   of hand-rolling `isCompact_Icc.image hg |>.isBounded.subset_closedBall 0` — this replaces ~3 lines
   of the inner `hbd` helper with the named mathlib lemma and documents the dependency. (A `/cleanup`
   nicety, not a correctness change; statement unchanged.)
3. **Consider marking it `private`** (or leaving it as a plain in-file helper) since it has a single
   in-file consumer and zero external callers — it is scaffolding for
   `normLeOne_frontier_lipschitz_cover_mixedSpace`, not public API.

Next action: do **not** PR this declaration to mathlib. Keep it as the file's local boundedness helper;
optionally golf its inner per-face step to use `IsCompact.exists_bound_of_continuousOn` directly
(a `/cleanup` task, statement-preserving).

---

## Next step

Do not PR `Chebotarev.exists_bound_frontierCoverFamily` to mathlib — mathlib already owns the general
theorem it instantiates (`IsCompact.exists_bound_of_continuousOn`, `Mathlib/Analysis/Normed/Group/Bounded.lean:96`).
Keep the lemma local to `ForMathlib/NormLeOneLipschitz.lean` as scaffolding for its single in-file
consumer; optionally golf the inner per-face boundedness step to call
`IsCompact.exists_bound_of_continuousOn` directly (statement-preserving `/cleanup`).
