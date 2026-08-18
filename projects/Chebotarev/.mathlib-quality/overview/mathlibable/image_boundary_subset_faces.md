# /mathlibable report — `Chebotarev.image_boundary_subset_faces`

> Step-9 mathlibable assessment (AINTLIB `/overview` pipeline). Single declaration.
> Source: `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:226`.
> Run under a stale local build: lean MCP project-decl tools (`lean_local_search`,
> `lean_goal`) and the mathlib-index search front-ends (`loogle`/`leansearch`) did
> not resolve in this environment; Phase 5 method [D] (grep over the vendored
> `.lake/packages/mathlib` source tree) was used as the load-bearing substitute, and
> reasoning proceeds from the source statement as instructed.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale (not rebuilt; per task instructions reason from source)
- decl `Chebotarev.image_boundary_subset_faces`:  ✓ resolved at `…/ForMathlib/NormLeOneLipschitz.lean:226`
- qualified name:           **`Chebotarev.image_boundary_subset_faces`** (VERIFIED — `namespace Chebotarev` opens at line 79, no inner namespace; matches the parsed guess)
- kind:                     `theorem`
- has sorry:                no
- module docstring summary: Lipschitz parametrization of the frontier of `normLeOne K` — covers the `realSpace` frontier of `normAtAllPlaces '' normLeOne K` by finitely many Lipschitz images of `[0,1]^{r-1}` (the GRS/Debaene boundary input).

---

### Statement (Phase 1)

`Chebotarev.image_boundary_subset_faces` is a **theorem** stating:

> Let `K` be a number field, `r = #InfinitePlace K`, `w₀` the distinguished infinite
> place, and `paramSet K ⊆ realSpace K` the mathlib parameter box
> `Iic 0 × [0,1)^{r-1}` (in the `completeBasis` coordinates) with
> `normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K)`. Then the
> `expMapBasis`-image of the **topological boundary** of the box,
> `closure (paramSet K) \ interior (paramSet K)`, is contained in the union of the
> images of the unit cube `[0,1]^{r-1}` under the bespoke face parametrizations:
> the `w₀`-face map `faceMapZero K` together with, for each non-distinguished place
> `i ≠ w₀` and each `a ∈ {0,1}`, the side-face map `faceMapSide K i a`.

In symbols:
```
expMapBasis '' (closure (paramSet K) \ interior (paramSet K))
  ⊆ faceMapZero K '' Icc 0 1
      ∪ ⋃ i : {w // w ≠ w₀}, ⋃ a ∈ ({0,1} : Set ℝ), faceMapSide K i a '' Icc 0 1
```

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — the ambient number field (a `variable` in the file).

Hypotheses (Lean side): none beyond the typeclasses — it is an unconditional set inclusion.

Conclusion (math): the image of the box boundary is covered by the finitely many compact-cube face parametrizations.
Conclusion (Lean): the `⊆` displayed above (a `Set (realSpace K)` inclusion).

**What the proof actually does** (lines 231–256): a boundary point `expMapBasis y`
has `y ∈ closure (paramSet K)` but `y ∉ interior (paramSet K)`; rewriting
`closure_paramSet`/`interior_paramSet` (mathlib lemmas) and pushing the negation
yields a coordinate `w` with `y w` on the boundary of its slot. Case split: if
`w = w₀` then `y w₀ = 0` and the point sits on the `w₀`-face (handled by
`faceMapZero` with `y` itself as cube coordinates); otherwise `y w ∈ {0,1}` and the
point sits on a side face, discharged by the private helper
`expMapBasis_mem_iUnion_faceMapSide` (lines 189–219), whose content is the
substitution `t = exp(y w₀) ∈ (0,1]` that linearizes the unbounded `w₀`-direction
into the freed cube slot `c i`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is an internal step of one file's proof — not a `def`/`class`, not a
`## Main results` entry (the main results are `normLeOne_frontier_lipschitz_cover*`),
not a named theorem. It is the "face covering" reduction lemma feeding
`frontier_subset_frontierCoverFamily`.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is a ~26-line
tactic proof.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "mathlib4 frontier image set covered by finitely many Lipschitz images of unit cube measure" | no | — | returns GMT papers (self-similar sets, Lipschitz graphs); no mathlib result and no *named* classical theorem for "box-boundary image ⊆ named face maps" |
| 2 | WebSearch (general/source form) | "Gun Ramaré Sivaraman counting ideals ray classes Lipschitz boundary Davenport Debaene fundamental domain" | yes | the *covering count* (boundary covered by `O(1)` Lipschitz images of `[0,1]^{n-1}`) is a step in the Davenport/Widmer/Debaene lattice-point method | arXiv:2208.06602 / JNT 243 (2023); confirms the **mathematical role**, not a reusable abstract lemma — the cover is built ad hoc for the number-field region |
| 3 | WebSearch (named-after / ambient API) | "mathlib NumberField mixedEmbedding normLeOne expMapBasis paramSet frontier volume canonical embedding" | partial | mathlib has `normLeOne`, `expMapBasis`, `paramSet`, `completeBasis`, `volume_frontier_normLeOne` | confirms the entire vocabulary of the statement is **mathlib NumberField API**, and that mathlib stops at the *qualitative* `volume_frontier_normLeOne` (measure-zero), not a quantitative cover |
| 4 | ChatGPT MCP | "standard form + generality + historical evolution of: boundary of the GRS/Debaene counting region is covered by finitely many Lipschitz images of the unit cube" | n/a | — | MCP unavailable in this environment (task-noted outage). Compensated by channels 1–3, 9, 10 + the local source quote in §References below. |
| 5 | Local references | grep `projects/Chebotarev/.mathlib-quality/references/` for "Lipschitz"/"boundary"/"Debaene" | n/a | — | no per-project PDF refs dir present in this checkout (refs are local-only/gitignored per AINTLIB CLAUDE.md and absent here) — recorded n/a |
| 6 | nLab | "Lipschitz image" / "boundary of fundamental domain" | no | — | nLab has no entry pairing a number-field fundamental-domain boundary with explicit cube parametrizations; not the kind of bespoke analytic lemma nLab catalogues |
| 7 | nCatLab | (categorical?) | n/a | — | not a categorical statement (a concrete set inclusion in `realSpace K`) |
| 8 | Stacks Project | (alg-geom?) | n/a | — | not an algebraic-geometry concept (real analytic geometry of the Minkowski embedding) |
| 9 | MathOverflow / MSE | "cover boundary of region by Lipschitz images of cube lattice point counting" | weak | — | the *technique* (Lipschitz-parametrizable boundary ⇒ boundary lattice-point error `O(M^{n-1})`) is folklore from Davenport's lemma / Widmer (GTM-style); always instantiated per-region, never as a standalone "image of THIS box ⊆ THESE face maps" lemma |
| 10 | recent arXiv (≤5 yr) | "effective ideal counting number field Lipschitz boundary fundamental cone" | yes | GRS 2022/23; related: Debaene, "Explicit counting of ideals…" | same conclusion as #2 — the boundary-cover is a proof step inside an analytic counting argument, specialised to the field's region; no abstract reusable statement is isolated |

The protocol passed: WebSearch ran 3 distinct queries at different generality
levels (#1 specific, #2 source/general, #3 ambient-API/named); ChatGPT MCP
attempted and recorded n/a with the outage reason and compensating channels;
local refs checked (absent → n/a with reason); nLab checked; Stacks / nCatLab /
MathOverflow / arXiv each checked or n/a with a reason.

### Literature summary (Phase 3)

Concept identified as: **the Lipschitz-boundary (a.k.a. "boundary covered by
finitely many Lipschitz images of `[0,1]^{n-1}`") input to the
Davenport–Widmer–Debaene lattice-point count**, here specialised to the boundary
of `normAtAllPlaces '' (normLeOne K)` via the mathlib `expMapBasis`/`paramSet`
parametrization. The specific statement — *this* box boundary's image lands in
*these named face maps* — is a bespoke proof step, not a named theorem.

Sources agree on the standard form: yes, on the *role* — in the literature one
exhibits, for the region being counted, finitely many `O(1)`-Lipschitz maps from
the unit cube whose images cover the boundary; this is what powers the boundary
error term `O(M^{n-1})`. They do **not** provide a reusable abstract lemma; the
cover is constructed inline for each region.

Most general standard form: "the frontier of a (nice, e.g. semialgebraic /
piecewise-`C¹`) bounded region in `ℝⁿ` is the union of finitely many Lipschitz
images of `[0,1]^{n-1}`" — a *generic* geometric-measure-theory fact (Lipschitz
`(n-1)`-rectifiability of the boundary). Our theorem is **far more specific** than
this: it does not assert generic rectifiability, it pins the cover to concrete,
named parametrizations `faceMapZero`/`faceMapSide` defined from the
number-field-specific `expMapBasis`.

Generality dimensions where the literature varies:
- region class: from "this specific number-field counting region" (GRS/Debaene)
  up to "any bounded semialgebraic / Lipschitz-rectifiable set" (generic GMT). Our
  decl sits at the *most specific* end and is welded to mathlib's `paramSet`/`expMapBasis`.
- ambient identification: the statement lives in `realSpace K` after the
  `normAtAllPlaces` reduction — a number-field-only stage.

Disagreement with the literature: none — the proof faithfully realises the
GRS §3.3 / Debaene boundary step; it simply does so as a project-local lemma in
mathlib's `paramSet` coordinates.

---

### Generality analysis — `Chebotarev.image_boundary_subset_faces`

Literature-standard form (from Phase 3): per-region exhibition of an explicit
finite Lipschitz cube cover of the boundary; the *generic* analogue is Lipschitz
`(n-1)`-rectifiability of a nice bounded set's frontier.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NumberField K]` | a number field | (none — the generic GMT statement has no field) | NO | the conclusion is *stated in terms of* `expMapBasis`, `paramSet`, `w₀`, `faceMapZero`, `faceMapSide`, all of which only exist for a number field. Removing `K` deletes the statement. |
| 2 | the set `closure (paramSet K) \ interior (paramSet K)` | the box boundary, mathlib's `paramSet` | "boundary of the region" | NO (in this form) | `paramSet K` *is* the region. One could phrase a generic "box boundary" lemma about `Iic a ×ˢ ∏ Ico 0 1`, but that is a *different* (and much more general) theorem — see Phase 4c/6, not a weakening of this one. |
| 3 | target: `faceMapZero ∪ ⋃ faceMapSide` | concrete named face maps | "finitely many Lipschitz images of `[0,1]^{n-1}`" | NO | the named maps carry the bespoke `t = exp(x w₀)` linearization; they are the construction, not a parameter to be relaxed. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it is** (it is already
unconditional in `K` and carries no removable hypotheses) — but it is also
**intrinsically narrow / project-specific**: every non-logical symbol in the
conclusion is a `Chebotarev`- or mathlib-`NumberField`-local construct, so there
is no "more general number field" or "weaker typeclass" to move to. It is not a
specialisation of a stronger statement that we should restate; it is a glue step.
Number of weakening opportunities found: 0.
Proposed restatement: n/a (no weakening target).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses? | no | — | already fully typeclass-driven (`[NumberField K]`); no bundled preamble to convert |
| 2 | sequences/metric → filters/topological? | no | — | already topological (`closure`/`interior`/image); no sequential content |
| 3 | construct object → universal-property class? | no | — | it's a set inclusion, not a construction of an object |
| 4 | set-with-predicate → bundled substructure? | no | — | the faces are images of maps, not a substructure-lattice candidate |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | — | inherently number-field; nothing to weaken to a (semi)ring/pseudometric |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | — | the indices (`InfinitePlace K`, `{0,1}`) are intrinsic finite sets, not a relaxable numeric index |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the statement is a concrete, already-topological set inclusion
whose vocabulary is entirely number-field-specific; there is no contemporary
mathlib reformulation that re-organises it without simply deleting its content.
(The one *adjacent* abstraction that mathlib *would* want — a generic
"image of a box-frontier under an open map ⊆ image of the face set" lemma — is a
**different theorem**, analysed in Phase 6; it would not be a restatement of this
one but a new general lemma that this one would then *consume*.)

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `Chebotarev.image_boundary_subset_faces`

[A] Lean-Finder       (unavailable in env)                                  n/a: stale-build env; MCP index front-end did not resolve
[B] Loogle            `Set.image _ (closure _ \ interior _) ⊆ _ ∪ _`        n/a: index front-end unavailable; pattern is in project-local symbols (`expMapBasis`, `faceMapSide`) that no mathlib index could host anyway
[C] LeanSearch        "image of box boundary under exp map contained in face parametrizations" n/a: front-end unavailable; concept is project-specific
[D] Grep mathlib src  `frontier.*image`, `image_frontier`, `closure.*interior.*diff`, `frontier_pi`, `interior_pi_set`, `closure_pi_set`, `frontier_Icc/Iio`, `IsOpenMap.*frontier` over `.lake/packages/mathlib/` | hits: only the **generic building blocks** (see below); **no** hit for the statement itself |
[E] Name pattern      grep `image_boundary_subset_faces`, `faceMapZero`, `faceMapSide`, `expMapBasis_mem_iUnion` across mathlib | no hits — names exist only in the project |

Searched for both:
- the user's current form (project-local symbols) → not in mathlib, and could not
  be, since `faceMapZero`/`faceMapSide`/`expMapBasis_mem_iUnion_faceMapSide` are
  defined in this very file.
- the literature-standard / generic form (open-map frontier image; box-frontier
  decomposition) → mathlib has the **pieces** but not an assembled lemma:
  - `Mathlib/Topology/Maps/Basic.lean` — `IsOpenMap.preimage_frontier_subset_frontier_preimage`, `preimage_frontier_eq_frontier_preimage`
  - `Mathlib/Topology/Homeomorph/Defs.lean:312` — `Homeomorph.image_frontier`
  - `Mathlib/Topology/Constructions.lean:1114` — `interior_pi_set`
  - `Mathlib/Topology/NhdsWithin.lean:411` — `closure_pi_set`
  - `Mathlib/Topology/Order/DenselyOrdered.lean` — `interior_Iic`, `frontier_Iio`, `frontier_Icc`
  - plus the mathlib **NumberField** lemmas this proof already calls by name:
    `closure_paramSet`, `interior_paramSet`, `expMapBasis_apply''`,
    `normAtAllPlaces_normLeOne_eq_image` (in `…/CanonicalEmbedding/NormLeOne.lean`).

Concluded: **not in mathlib** (all available methods exhausted, plus the
generic/literature form). Mathlib stops at the *qualitative* boundary result
`volume_frontier_normLeOne` (frontier has measure zero); the *quantitative* finite
Lipschitz-cube cover — of which this lemma is the combinatorial heart — is
genuinely absent. The exact form, however, is **inexpressible in mathlib** as
written because its conclusion names three project-local definitions.

---

### Call sites — `Chebotarev.image_boundary_subset_faces`

Internal use count: **1** (within the same project, NOT counting… — but note it is
**inside the declaring file**): `…/ForMathlib/NormLeOneLipschitz.lean:320`, in the
proof of `frontier_subset_frontierCoverFamily`.
External-to-file callers: **0** distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| NormLeOneLipschitz.lean:320 | `((image_boundary_subset_faces K).trans (Set.union_subset ?_ ?_))` — the single consumer |
| NormLeOneLipschitz.lean:310 | (docstring mention only, in `frontier_subset_frontierCoverFamily`'s doc) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?): (none).

**Signal:** K = 1 use, and that one use is *in the same file*, with **0**
external-to-file and **0** cross-project callers. Per the call-sites table this is
the "K = 1 internal use only ⇒ possibly the wrong granularity / could be inlined"
pattern, reinforced by it being a same-file private-style step (its sibling helper
`expMapBasis_mem_iUnion_faceMapSide` is literally `private`). It is plumbing for
the file's own `normLeOne_frontier_lipschitz_cover`, not a reused API surface.

---

### Composition check (Phase 6)

Can `Chebotarev.image_boundary_subset_faces` be derived from mathlib in ≤3 chained
calls? **No — but that is the wrong question here**, because the *statement itself*
is not a mathlib statement (it mentions `faceMapZero`/`faceMapSide`). The honest
composition question is: *is this lemma's mathematical content a thin assembly of
mathlib primitives, such that it should not be a standalone mathlib lemma?*

Attempt 1 (generic skeleton from mathlib pieces):
`expMapBasis '' (closure paramSet \ interior paramSet)` → rewrite the box frontier
via `closure_paramSet` + `interior_paramSet` + `interior_pi_set`/`closure_pi_set` +
`frontier_Iio`/`frontier_Icc`, distribute the image (`Set.image_union`,
`Set.image_iUnion`), and identify each face slice.
- Mathlib decls used: `interior_pi_set`, `closure_pi_set`, `interior_Iic`,
  `frontier_Iio`, `frontier_Icc`, `Set.image_union`, `Set.image_iUnion`, plus the
  NumberField lemmas `closure_paramSet`, `interior_paramSet`, `expMapBasis_apply''`.
- Result: **partial** — these reduce the *topology* of the box frontier, but they
  do NOT produce the `faceMapSide` parametrization. The substantive content — that
  on a side face the unbounded `w₀`-direction re-parametrizes as the cube slot via
  `t = exp(x w₀)` (the private `expMapBasis_mem_iUnion_faceMapSide`, ~30 lines of
  genuine `funext`/case reasoning) — is a real proof, not a composition.
- Notes: well over 3 chained calls, and the core step is irreducibly bespoke.

Conclusion: **NOT-COMPOSABLE** (as a ≤3-call mathlib derivation). The lemma is not
a mechanical composition; it is a genuine, if specialised, proof. **However**, the
generic shell around it *is* the kind of thing mathlib could host (an open-map /
box-frontier image lemma) — see the verdict.

---

## Verdict: `Chebotarev.image_boundary_subset_faces`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the boundary-cover is a per-region *proof step* in
  the Davenport–Widmer–Debaene/GRS counting method, never a reusable abstract
  theorem; its statement here is welded to mathlib's `paramSet`/`expMapBasis` and
  to two project-local face definitions.
- Generality analysis (Phase 4): already unconditional in `K`, no weakening target,
  and no modern-idiom restatement — it is intrinsically a number-field glue lemma,
  not a specialisation of a more general result we should upstream.
- Mathlib search (Phase 5): not in mathlib, and *cannot be stated* in mathlib as
  written (conclusion names `faceMapZero`/`faceMapSide`); mathlib does provide the
  generic frontier / box / open-map building blocks and the NumberField API this
  proof already consumes.
- Composition check (Phase 6): NOT a ≤3-call composition (the `faceMapSide`
  substitution is a real ~30-line argument) — but it is bespoke plumbing with a
  single same-file consumer and zero external callers.

**Rationale (1–2 paragraphs):**

This theorem is a project-internal step in `NormLeOneLipschitz.lean`'s proof that
the frontier of `normAtAllPlaces '' (normLeOne K)` is covered by finitely many
Lipschitz images of the unit cube (`normLeOne_frontier_lipschitz_cover`, the GRS
§3.3 / Debaene boundary input feeding the effective lattice-point count). Its
conclusion is phrased entirely in terms of three constructs that have no meaning
outside this development — `expMapBasis`/`paramSet` (mathlib NumberField API, but
only sensible for a number field) and `faceMapZero`/`faceMapSide` (defined ~80
lines above in the same file). It is therefore *not a candidate to add to mathlib
as-is*: mathlib cannot even state it without first importing the project's bespoke
face parametrizations. The literature confirms this is a proof step, not a named
result: GRS and Debaene exhibit such a cube cover inline for the specific counting
region; nobody isolates "the image of *this* box boundary lands in *these* face
maps" as a standalone lemma. Mathlib's own treatment of the same region stops at
the *qualitative* `volume_frontier_normLeOne` (measure zero) and never builds the
quantitative cover.

It lands in `NO-composable-from-mathlib` rather than a YES bucket because, although
the lemma is a genuine (non-trivial) proof rather than a literal 1–3-call
composition, its *role* is exactly that of inlinable glue: a single consumer in the
same file, zero external/cross-project callers, and a sibling helper that is
already `private`. The reusable mathematics buried inside it is **not** this
number-field-specific inclusion but two *generic* facts mathlib is currently
missing and that the proof open-codes: (a) for an open injective map `f` with
`univ` source, `f '' (closure S \ interior S) ⊆ f '' (frontier-of-box decomposition)`
(an `IsOpenMap`/`OpenPartialHomeomorph` frontier-image lemma — mathlib has the
`preimage` direction in `Topology/Maps/Basic.lean` and `Homeomorph.image_frontier`,
but not this image-side box version), and (b) the frontier of a product box
`Iic a ×ˢ ∏ Ico 0 1` as the explicit union of its faces (mathlib has
`interior_pi_set`/`closure_pi_set`/`frontier_Iio`/`frontier_Icc` but not the
assembled `frontier_pi_box`). Those generic lemmas would be the right mathlib
contributions; *this* declaration is their number-field application and should stay
in the project.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the project-specific residue (`faceMapSide`'s
`t = exp(x w₀)` substitution) is genuinely bespoke and belongs to the project. The
declaration is glue plumbing — keep it in the project, do **not** upstream it as
written.

Mathlib building blocks (with full paths):
- `Mathlib/Topology/Constructions.lean:1114` — `interior_pi_set`
- `Mathlib/Topology/NhdsWithin.lean:411` — `closure_pi_set`
- `Mathlib/Topology/Order/DenselyOrdered.lean` — `interior_Iic`, `frontier_Iio`, `frontier_Icc`
- `Mathlib/Topology/Maps/Basic.lean:449,455` — `IsOpenMap.preimage_frontier_subset_frontier_preimage`, `…eq_frontier_preimage`
- `Mathlib/Topology/Homeomorph/Defs.lean:312` — `Homeomorph.image_frontier`
- NumberField API already used by the proof: `closure_paramSet`, `interior_paramSet`,
  `expMapBasis_apply''`, `normAtAllPlaces_normLeOne_eq_image`
  (`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`).

Composition sketch: there is **no ≤3-line mathlib composition** that yields the
project's exact conclusion (the `faceMapSide` linearization is irreducible).
Concretely the refactor is therefore **not** "inline a mathlib one-liner" but:

Refactor plan (the actionable recommendation):
1. **Keep `image_boundary_subset_faces` in the project.** It is the correct home
   for the number-field-specific content; with a single same-file consumer it could
   even be marked `private` (like its sibling `expMapBasis_mem_iUnion_faceMapSide`)
   — that is a `/cleanup` call, not a `/mathlibable` action.
2. **If/when upstreaming effort is spent**, extract the two *generic* lemmas
   identified above as the mathlib contributions —
   `IsOpenMap.image_frontier_subset` (image-side box-frontier lemma) and a
   `frontier_pi`/`frontier`-of-product-box decomposition — and have this project
   lemma *consume* them. Those are separate `/mathlibable` candidates in their own
   right (and would each be `YES-but-generalise-first` / `YES-add-as-is` material),
   **not** this declaration.

Next action: leave `Chebotarev.image_boundary_subset_faces` in the project (it is
not mathlib-bound as stated). Optionally file a forward-looking note to extract the
generic open-map box-frontier lemma + product-box frontier decomposition as
independent mathlib contributions; this decl would then be re-proved as a thin
application of them but still live in the Chebotarev project.

---

## Next step

Leave the declaration in the project — it is number-field-specific glue whose exact
statement is inexpressible in mathlib (it names `faceMapZero`/`faceMapSide`). Do not
upstream as-is. The mathlib-worthy content is the *generic* open-map box-frontier
image lemma and product-box frontier decomposition it open-codes; track those as
separate contributions if/when the effort is spent.
