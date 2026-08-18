# /mathlibable report — `Chebotarev.faceMapSide`

## Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source)
- decl `Chebotarev.faceMapSide`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:146`
- kind:                      `def` (noncomputable section; `open scoped Classical in`)
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` —
  covers `frontier (normAtAllPlaces '' normLeOne K)` by finitely many `M`-Lipschitz images of
  the unit cube `[0,1]^{r-1}`. The author-earmarked ForMathlib input of the effective
  lattice-point count.

Qualified name **verified from source**: namespace `Chebotarev` (line 79 `namespace Chebotarev`,
no nested namespace before line 146) ⇒ `Chebotarev.faceMapSide`. (Task's parsed guess confirmed.)

---

## Statement (Phase 1)

`Chebotarev.faceMapSide` is a **definition**: a parametrization, by the unit cube
`[0,1]^{r-1}` (`r = #InfinitePlace K`), of the `expMapBasis`-image of a single *side face*
`{x | x i = a}` (`i ≠ w₀`, `a ∈ {0,1}`) of the box `paramSet K = Iic 0 × [0,1)^{r-1}`
(in the `completeBasis K` coordinates).

The geometry: mathlib's parametrization gives
`normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K)`. The box boundary splits into
the `w₀`-face `{x w₀ = 0}` (handled by `faceMapZero`) and the side faces `{x i = a}`. On a side
face the distinguished `w₀`-direction is the *unbounded* ray `Iic 0`, so `expMapBasis` restricted
there is not a map out of a compact cube. The substitution `t = exp (x w₀) ∈ (0,1]` linearizes it:
using `expMapBasis x = exp (x w₀) • expMapBasis (x [w₀ ↦ 0])` (`expMapBasis_apply''`), the face
image is reparametrized so the freed cube slot `c i` carries `t`. Concretely

```
faceMapSide i a c = (c i) • expMapBasis (fun w ↦ if w = w₀ then 0
                                                 else if ⟨w,_⟩ = i then a
                                                 else c w)
```

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K] [NumberField K]` — the number field.
- `i : {w : InfinitePlace K // w ≠ w₀}` — which side face (a non-distinguished infinite place).
- `a : ℝ` — the pinned coordinate value (used at `a ∈ {0,1}`, but the def is stated for all `a`).
- `c : {w : InfinitePlace K // w ≠ w₀} → ℝ` — the cube point.

Hypotheses (Lean side): none (it is a total `def`; `a`/`c` unconstrained).

Conclusion (math): a point of `realSpace K = InfinitePlace K → ℝ`.
Conclusion (Lean): `realSpace K` (n/a — definition).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper construction (one of the `M` constituent maps of the cover), not itself a
named theorem or a new mathematical *structure*; it is plumbing for the file's main results.
(Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Body line count: **1 substantive line** (a single `c i • expMapBasis (fun w ↦ …)` expression).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | not sealed for unification control; `faceMapSide` is *unfolded* directly (`rw [faceMapSide]` at line 217, `change faceMapSide …` at line 336) — the opposite of a defeq barrier. |
| Avoid typeclass diamonds          | no       | no instance resolution rides on it; it returns a plain `realSpace K` value. |
| Mark semantic intent / API name   | partial  | it *does* have a name + docstring and is referenced by name across the file (`contDiff_faceMapSide`, `expMapBasis_mem_iUnion_faceMapSide`, `frontierCoverFamily`), but every consumer is **inside the same file** — no cross-module API surface. |

Conclusion: **ONE-LINER WITH-EXEMPTION (weak)** — the "semantic intent" exemption applies only
file-locally. Carried into Phase 7: the one-liner is a legitimate *internal* abstraction but has
no standalone cross-module API role, which pushes against a clean YES-add-as-is and toward
BORDERLINE / package-with-the-theorem.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Lipschitz parametrization boundary fundamental domain number field lattice point counting Davenport" | yes | boundary `∂S` is **Lipschitz-parametrizable**: covered by finitely many Lipschitz maps from a cube | Widmer, *Lipschitz class, narrow class, and counting lattice points* (PAMS 140, 2012); Davenport's classical principle |
| 2 | WebSearch (general form) | "boundary covered finitely many Lipschitz images unit cube … Widmer Masser Vaaler" | yes | class `Lip(n,M,L)`: `M` maps `φᵢ : [0,1]^{n-1} → ℝ^n`, common Lipschitz const `L`, covering `S`; ⇒ `|#(Λ∩S) − vol/det| ≪ …` | Masser–Vaaler; Widmer; the exact "Principle of Lipschitz" the file invokes |
| 3 | WebSearch (named-after / aliases) | "\"Lipschitz parametrizable\" boundary \"Lip(M,L)\" counting lattice points o-minimal" | yes | `S ∈ Lip(n,M,L)` iff `∃ φ₁…φ_M : [0,1]^{n-1}→ℝ^n` with `|φᵢ(x)−φᵢ(y)| ≤ L|x−y|`, `S ⊆ ⋃ im φᵢ` | exact textbook definition; o-minimal variant (Barroero–Widmer) noted |
| 4 | WebSearch (source paper) | "Gun Ramaré Sivaraman counting ideals ray classes Debaene Lipschitz boundary fundamental domain face parametrization" | yes | the cited source: GRS *Counting ideals in ray classes*, JNT 243 (2023/2022), computes the Lipschitz class of `∂F` for the fundamental domain `F`, after Debaene | confirms the file's reference §3.3; parametrizes `∂F` but **not** via mathlib's `expMapBasis`/`w₀` encoding |
| 5 | WebSearch (precise defn) | "Masser Vaaler \"Lip(n,M,L)\" definition maps unit cube Lipschitz constant …" | yes | same `Lip(D,M,L)` definition verbatim; "boundaries of cubes are in `Lip(...)` with `M=2n+2`, `L=2`" | the side-faces-of-a-box decomposition is exactly the classical cube-boundary argument |
| 6 | ChatGPT math MCP | (standard form + generality + history) | n/a | — | MCP down per task brief; substituted with extra WebSearch queries #4–#5 (5 web queries total, ≥3 generality levels covered). |
| 7 | Local references | `.mathlib-quality/references/` and `refs/Chebotarev/` | n/a | — | both directories absent on this checkout (confirmed: `ls` → No such file or directory). Recorded n/a. |
| 8 | nLab | "Lipschitz parametrizable boundary" / "Principle of Lipschitz" | n/a | — | not an nLab topic (analytic number theory / geometry of numbers, not a categorical concept). Searched, no clean abstract page; n/a with reason. |
| 9 | Stacks Project | — | n/a | — | not an algebraic-geometry concept (geometry of numbers / real analysis). |
| 10 | nCatLab | — | n/a | — | not categorical. |
| 11 | MathOverflow / MSE | "Lipschitz parametrizable boundary lattice point counting" | yes (folded into #1–#3 results) | same Masser–Vaaler/Widmer framing surfaced | no distinct new form. |
| 12 | recent arXiv (≤5y) | "counting lattice points o-minimal Lipschitz boundary" | yes | Barroero–Widmer o-minimal *Principle of Lipschitz* (arXiv:1210.5943) — replaces explicit face maps by o-minimal definability | a *different proof strategy* that avoids constructing maps like `faceMapSide` at all. |

### Literature summary (Phase 3)

Concept identified as: the **Principle of Lipschitz** / **Lipschitz class `Lip(n,M,L)`**
(Davenport; Masser–Vaaler; Widmer) — the *cover* of a boundary by `M` Lipschitz images of
`[0,1]^{n-1}`. For *this particular* boundary (the fundamental cone / `normLeOne` frontier),
the relevant source is **Gun–Ramaré–Sivaraman §3.3 (after Debaene)**.

Sources agree on the standard form: **yes** — for the *aggregate* object (the `Lip(n,M,L)`
cover). The **individual constituent map** `faceMapSide` (one `φᵢ`, built by pinning a box
coordinate and exponential-substituting the `w₀`-ray) is **not a named object** in the
literature: papers either (a) bound the Lipschitz class of `∂F` wholesale via explicit but
ad-hoc face maps tied to *their* coordinates on `F`, or (b) invoke o-minimal definability and
construct no maps at all. There is **no literature-standard `faceMapSide`** — it is an artifact
of mathlib's specific `expMapBasis : Iic 0 × [0,1)^{r-1} → realSpace K` parametrization.

Most general standard form: "`∂S ∈ Lip(n,M,L)`" as a *property of the set*, discharged however
is convenient. The literature does **not** fix a canonical parametrizing map.

Generality dimensions where the literature varies:
- **parametrization vs. property**: some state Lipschitz-parametrizability as a property of `S`
  (most general — `faceMapSide` is one *witness* of it), others exhibit explicit maps.
- **explicit faces vs. o-minimal**: modern treatments (Barroero–Widmer) skip explicit maps
  entirely; the explicit-face approach (this file, GRS) is the classical route.

Disagreement with the literature: none mathematically; the file's `faceMapSide` is a *correct
witness*, but its exact shape is dictated by mathlib's encoding, not by any source.

---

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the relevant *theorem* is "the frontier is in
`Lip(r−1, M, L)`"; `faceMapSide` is one witnessing map, **not** a statement to be generalized in
the typeclass sense.

### 4a/4b — Generality status

| # | Parameter | Current Lean form | Literature analog | Weaker form? | Reason |
|---|-----------|-------------------|-------------------|--------------|--------|
| 1 | `[Field K] [NumberField K]` | a number field | number fields (the whole problem is number-field-specific) | NO | `expMapBasis`, `w₀`, `paramSet` are all number-field objects; no weaker base makes sense. |
| 2 | `i : {w // w ≠ w₀}` | a non-distinguished place | "a non-`w₀` box coordinate" | NO | intrinsic to the box `Iic 0 × [0,1)^{r-1}` indexing. |
| 3 | `a : ℝ` | a real | the pinned value `∈ {0,1}` | (already maximally loose) | def is stated for *all* `a` though only `a∈{0,1}` is used — already as general as the construction allows. |
| 4 | `c : {w // w ≠ w₀} → ℝ` | cube point | `[0,1]^{r-1}` point | (def total) | already total; restriction to `Icc 0 1` happens at use sites. |

Generality verdict (Phase 4b): the def is **as general as it can be** in the typeclass sense
(there is no weaker base structure — it is irreducibly about a number field's `expMapBasis`
parametrization). It is **NOT** "maximally general" in the *useful* mathlib sense, because the
right mathlib object is the **property / theorem** (frontier `∈ Lip(...)`), and `faceMapSide` is
an internal witness whose signature is coupled to mathlib's `expMapBasis` encoding.
Cost of any restatement: n/a (no typeclass weakening available).

### 4c — Modern mathlib-idiom restatement (Bourbaki 2.0)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | "let X be a foo" → typeclass? | no | already a clean `def`; nothing to bundle. | — |
| 2 | sequences/metric → filters/topology? | no | already uses `LipschitzWith` / `ContDiff` (the right mathlib idioms). | — |
| 3 | construction → universal-property class? | **partially relevant** | the *aggregate* could be phrased as "the set is `IsLipschitzParametrizable`/in a `Lip` class" — but **mathlib has no such predicate yet**; that would be a *new* abstraction (the real upstreaming target), with `faceMapSide` an internal witness. | a `Lip(n,M,L)` API + a Davenport/Widmer counting lemma would be the genuinely mathlib-worthy contributions — not this constructor. |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure. | — |
| 5 | vector/metric-specific → weaken typeclass? | no | already `realSpace K = InfinitePlace K → ℝ`; no scalar generality to extract. | — |
| 6 | 1-categorical → higher-categorical? | no | n/a. | — |
| 7 | concrete index → general monoid? | no | the index `{w ≠ w₀}` is intrinsic. | — |

Modern-idiom verdict (Phase 4c): **the modernization that matters is one level up** — mathlib
would benefit from a reusable `Lip(n,M,L)`/"boundary is finitely-Lipschitz-covered" predicate and
the associated Davenport-style counting estimate (cf. `volume_frontier_normLeOne` only gives
measure-zero today). Within that, `faceMapSide` is an **implementation detail**, not the API.
There is no idiom that makes `faceMapSide` itself a cleaner standalone export. Real improvement:
yes, but it lives in the *theorem/predicate*, not this def.

---

## Diamond / defeq risk (Phase 4.5 — kind is `def`)

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | returns a plain `realSpace K` value; introduces no instance. |
| 2 | Reducibility leak | low | not `@[reducible]`; the file deliberately `rw [faceMapSide]`/`change` to unfold (lines 217, 336), so semi-reducible behaviour is intended and contained. |
| 3 | Non-canonical unfolding | low | the nested `if/dite` body could surprise `simp`, but it is only ever unfolded explicitly; no `@[simp]` attribute. |
| 4 | Instance priority | n/a | not an `instance`. |
| 5 | Universe issues | none | everything is `Type`-level concrete (`realSpace K`). |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`. |

Risk verdict (Phase 4.5): **LOW**. No HIGH rows. (Doesn't gate the verdict.)

---

## Mathlib search-status (Phase 5)

Five-method search (mathlib MCP tools `lean_loogle`/`lean_leansearch` were **not available** as
deferred tools in this environment — only WebSearch resolved; substituted method [D] grep over
the pinned mathlib tree, which is authoritative for this NumberField-specific concept):

- [A] Lean-Finder — n/a (tool unavailable in env).
- [B] Loogle — n/a (tool unavailable in env). Intended pattern:
  `(InfinitePlace _ → ℝ) → (InfinitePlace _ → ℝ)` cube parametrization.
- [C] LeanSearch — n/a (tool unavailable in env).
- [D] **Grep mathlib src** — searched the pinned tree
  `.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/`:
  - `faceMap` / `faceMapSide` / `faceMapZero`: **0 hits anywhere in mathlib**.
  - the parametrization substrate **does** exist: `expMapBasis` (NormLeOne.lean:465),
    `paramSet` (:635), `normLeOne` (:164), and crucially `expMapBasis_apply''` (:504) — the exact
    lemma `faceMapSide` is built on.
  - the *aggregate* result is **absent**: mathlib has only `volume_frontier_normLeOne`
    (measure-zero of the frontier), the strictly-weaker statement the module docstring contrasts
    against. No frontier-Lipschitz-cover, no `Lip(n,M,L)` predicate.
- [E] Name pattern — grep for `faceMap`/`*MapSide`/`frontier.*[Ll]ipschitz.*cube` in mathlib:
  **0 hits**.

Searched for both forms:
- user's form (`faceMapSide` constructor): **not in mathlib**.
- literature-standard form (frontier `∈ Lip(n,M,L)` / a Lipschitz-cover predicate): **not in
  mathlib** (only the measure-zero `volume_frontier_normLeOne` exists).

Concluded: **not in mathlib** (grep + name-pattern exhausted; the building blocks
`expMapBasis`, `expMapBasis_apply''`, `paramSet` are present, but neither `faceMapSide` nor the
theorem it serves exists).

---

## Composition check (Phase 6)

### 6.0 Call sites — `Chebotarev.faceMapSide`

Internal use count: **0 outside the declaring file** (grep across the whole repo, excluding the
declaring file, returns nothing).
External-to-file callers: **0 files**.

Within the declaring file `NormLeOneLipschitz.lean`, `faceMapSide` is load-bearing — referenced
at 10+ sites:

| Site (declaring file) | Usage |
|------------------------|-------|
| :159 `contDiff_faceMapSide` | proves the map is `C¹` (so Lipschitz on the cube). |
| :189–194 `expMapBasis_mem_iUnion_faceMapSide` | every boundary image point lands in some `faceMapSide i a '' Icc 0 1`. |
| :204, :217 | `faceMapSide K i (y w) c = expMapBasis y` (the linearization identity). |
| :226–230 `image_boundary_subset_faces` | box-boundary image ⊆ `faceMapZero ∪ ⋃ faceMapSide …`. |
| :284–289 `frontierCoverFamily` | `faceMapSide` is the `inr (inr …)` arm of the finite cover family. |
| :300 `exists_lipschitzWith_frontierCoverFamily` | uniform Lipschitz constant over the side faces. |
| :336, :542 | final assembly of the cover theorem. |

Inline-derivation grep (re-derived elsewhere without `faceMapSide`?): **none** — it is the unique
internal name for this construction; consumers all go through it.

Call-sites signal: **K = 0 external, but a genuine *file-internal* API** with no inline
re-derivation. Per the Phase-6.0.1 table this is the "right abstraction, but its consumers are
all local" pattern — not dead code (it threads through the file's main results), yet not a
cross-module API either. This is the central tension for the verdict.

### 6a Composition attempt

Can `faceMapSide` be derived from mathlib in ≤3 chained calls? It is a **definition**, so the
relevant question is "is its *defining expression* a trivial mathlib composition that should be
inlined?" The body is `c i • expMapBasis (fun w ↦ if … then 0 else if … then a else c …)` —
a scalar-smul of `expMapBasis` applied to a pinned-coordinate reindexing.

- Attempt 1: inline the body at the (file-internal) call sites instead of naming it.
  - Result: **fails as a "remove it" move** — the *theorems about it*
    (`contDiff_faceMapSide`, the `iUnion` membership lemma, the cover assembly) genuinely need a
    stable name to state and reuse; inlining the nested `dite/ite` at 10+ sites would be a
    regression, not a simplification. The accompanying proofs (`expMapBasis_apply''` rewrite,
    the `funext` coordinate bookkeeping at :206–217) are *real work*, not a 1–3 call chain.

Conclusion: **NOT-COMPOSABLE** (as a "this is just `mathlib_f (mathlib_g …)`, delete it" claim).
The def is a legitimate abstraction; it is not redundant with any mathlib primitive.

---

## Verdict: `Chebotarev.faceMapSide`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *cover* concept (`Lip(n,M,L)` / Principle of Lipschitz) is
  standard (Masser–Vaaler, Widmer, GRS §3.3); the *constituent map* `faceMapSide` is **not** a
  named literature object — its shape is dictated by mathlib's `expMapBasis`/`paramSet` encoding.
- Generality analysis (Phase 4): no typeclass weakening available; the genuinely mathlib-worthy
  object is one level up (the frontier `∈ Lip(...)` theorem / a Lipschitz-cover predicate), of
  which `faceMapSide` is an internal witness.
- Mathlib search (Phase 5): **not in mathlib** — and neither is the theorem it serves (mathlib has
  only the weaker `volume_frontier_normLeOne`); the substrate `expMapBasis`, `expMapBasis_apply''`,
  `paramSet` is present.
- Composition check (Phase 6): NOT-COMPOSABLE (a real abstraction), but **0 external call sites** —
  a file-internal API only.

**Rationale:**

`faceMapSide` sits in the awkward middle. It is mathematically meaningful and *not* redundant: it
is the explicit reparametrization (pin a box face, exponential-substitute the unbounded `w₀`-ray
via `expMapBasis_apply''`) that turns one face of mathlib's `Iic 0 × [0,1)^{r-1}` box into a
Lipschitz image of the compact cube. Mathlib has neither it nor the frontier-Lipschitz-cover
theorem it feeds. So it is not NO-mathlib-has-it and not NO-composable-from-mathlib.

But it is also **not** a clean YES. The literature names the *aggregate* (`Lip(n,M,L)`), never this
individual map; `faceMapSide`'s entire signature is welded to mathlib's specific `expMapBasis`/
`w₀`/`paramSet` formulation, and its only consumers are the other lemmas *in the same file*. The
right mathlib contribution is the **theorem** `normLeOne_frontier_lipschitz_cover` (and possibly a
reusable Lipschitz-cover predicate generalizing `volume_frontier_normLeOne`) — and *if* that whole
development is upstreamed, `faceMapSide` would plausibly travel with it as an internal/`private`
construction or be restructured, not exported as standalone public API. Whether to (a) upstream the
entire frontier-cover development (with `faceMapSide` as a supporting def), (b) keep it local to
AINTLIB, or (c) first build a general `Lip` predicate in mathlib and rephrase — is a packaging and
roadmap judgment the author must make. That is precisely a BORDERLINE call, not a property of the
def in isolation. (The Phase-2b one-liner status with 0 external callers reinforces this: as a
*standalone* export it is thin; its value is entirely as a piece of the larger proof.)

**Numbered questions for the author (≤5):**

1. Do you intend to upstream the **whole** frontier-Lipschitz-cover development
   (`normLeOne_frontier_lipschitz_cover` and its scaffolding) to mathlib as one PR — in which case
   `faceMapSide` ships as an internal supporting `def` (likely `private` or in a `…/NormLeOne/`
   helper file), not as standalone public API?
2. Should the target instead be a **reusable mathlib predicate** (e.g. a `Lip(n,M,L)` /
   "boundary is covered by finitely many `L`-Lipschitz cube images" structure) plus a Davenport/
   Widmer-style counting lemma — strengthening the existing `volume_frontier_normLeOne` — with
   `faceMapSide` rephrased as a witness for the `normLeOne` instance of that predicate?
3. If `faceMapSide` does go to mathlib, are you content with its signature staying coupled to
   `expMapBasis`/`paramSet`/`w₀` (i.e. it is explicitly a helper *for that parametrization*, not a
   general-purpose object)?
4. Is the `a : ℝ` argument intended to remain unconstrained (stated for all `a`, used at `{0,1}`),
   or would mathlib prefer it pinned to `a ∈ ({0,1} : Set ℝ)` / a `Bool` at the type level?

**Next action:** author answers Q1–Q4. If Q1 = "yes, ship the whole development" → the unit of
upstreaming is `normLeOne_frontier_lipschitz_cover` (run `/mathlibable` on *that* theorem, and on
the proposed cover predicate), with `faceMapSide` carried along as an internal piece — re-run
`/mathlibable Chebotarev.faceMapSide` only to confirm it should be `private`/non-exported.
