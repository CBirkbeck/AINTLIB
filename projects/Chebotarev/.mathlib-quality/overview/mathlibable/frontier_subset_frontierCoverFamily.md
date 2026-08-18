# /mathlibable report — `Chebotarev.frontier_subset_frontierCoverFamily`

_Step-9 overview mathlibable assessment, single declaration. Local Lean build is
stale (toolchain `v4.31.0-rc2`, mathlib pin `d90090f`; lib-target globbing for
`CebotarevDensity` does not resolve the module path here), so Phase 0 reasons
from source per the task note. ChatGPT-math MCP was **down** for this run
(Codex stdin failure, same as the sibling `frontier_image_paramSet_subset` /
`exists_card_inter_smul_lattice_sub_volume_mul_pow_le` runs) — the literature
phase was carried by WebSearch (≥3 queries at varying generality) + verbatim
PDF extraction of Widmer's definition via local `pdftotext` + nLab/MO + arXiv,
which together pin the standard form precisely._

## Baseline (Phase 0)
- lake build:               not run (stale; reasoned from source — mathlib pin `d90090f647ca`)
- decl `Chebotarev.frontier_subset_frontierCoverFamily`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:314`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` —
  covering the `realSpace` frontier `normAtAllPlaces '' (normLeOne K)` by finitely many
  Lipschitz images of the unit cube `[0,1]^{r-1}` (Gun–Ramaré–Sivaraman §3.3, after Debaene;
  Widmer / Lang lattice-point boundary input).

Namespace: the file opens `namespace Chebotarev` at line 79; the declaration is at line 314,
inside that block (the block closes `end Chebotarev` at line 673). The parsed qualified name
**`Chebotarev.frontier_subset_frontierCoverFamily` is CORRECT** (verified from source).

---

## Statement (Phase 1)

`Chebotarev.frontier_subset_frontierCoverFamily` states: for a number field `K` (with
`r = #InfinitePlace K`), the topological frontier of the `realSpace`-image of the norm-`≤ 1`
fundamental-cone region, `normAtAllPlaces '' (normLeOne K) ⊆ realSpace K = (InfinitePlace K → ℝ)`,
is contained in the union of the cube-images of the finite family `frontierCoverFamily K`:

> `frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ s, frontierCoverFamily K s '' Icc 0 1`,

where the index `s` ranges over the finite type `Unit ⊕ Unit ⊕ ({w // w ≠ w₀} × Bool)` and each
member `frontierCoverFamily K s : (Fin (r-1) → ℝ) → realSpace K` is the zero map, the `w₀`-face
map, or a side-face map, post-clamped to the unit cube and relabelled through `cubeRelabel`.

By the companion `exists_lipschitzWith_frontierCoverFamily` (line 295), every family member is
`M`-Lipschitz for a **common** constant `M : ℝ≥0`. Hence, read together, the pair
`(frontier_subset_frontierCoverFamily, exists_lipschitzWith_frontierCoverFamily)` is exactly the
assertion that **the frontier of `normAtAllPlaces '' normLeOne K` lies in the Lipschitz class
`Lip(r, m, L)`** in Widmer's sense (finitely many maps `[0,1]^{r-1} → ℝ^r` of common Lipschitz
constant covering the boundary). This theorem supplies the *cover-inclusion* half; the sibling
supplies the *common-constant* half. It is the bespoke discharge, for this one number-field set,
of the abstract `hlip` hypothesis of the effective lattice-point count.

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K]` — the number field.
- `normAtAllPlaces`, `normLeOne K`, `expMapBasis`, `paramSet K` — all **mathlib** objects from
  `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne` (imported line 3).
- `frontierCoverFamily K`, `faceMapZero`/`faceMapSide`, `clampUnit`, `cubeRelabel`, `w₀` — all
  **project-local** constructions defined earlier in this same file.

Hypotheses (Lean side): none beyond the instances (an unconditional set inclusion).

Conclusion (math): the boundary of the realSpace image of the norm-`≤1` cone is covered by the
unit-cube images of the explicit finite face family.

Conclusion (Lean): `frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ s, frontierCoverFamily K s '' Icc 0 1`.

Proof (≈25 lines, lines 317–341; for the composition analysis): a three-link chain —
1. `normAtAllPlaces_normLeOne_eq_image` (mathlib) rewrites the set to `expMapBasis '' paramSet K`;
2. `frontier_image_paramSet_subset` (project, line 174) reduces the frontier to the box-boundary
   image `∪ {0}`;
3. `image_boundary_subset_faces` (project, line 226) splits the box-boundary image into the
   `w₀`-face image, the side-face images, and `{0}`;
then each piece is matched to its family member by undoing `cubeRelabel` (`exists_cubeRelabel_eq`,
line 274) and the clamp (`clampUnit_eq_self`, line 94, with `cubeRelabel_mem_Icc`, line 269), with
`{0}` realised as the value of the zero map. No analytic content; it is set-algebra plumbing that
glues three already-proved lemmas to the explicit family.

---

## Size classification (Phase 2a)

Verdict: **SMALL** (helper / assembly lemma).
Reason: it is the **final assembly** step of the file's frontier-cover pipeline — not itself a
listed `## Main result` (the module docstring's Main results are the three
`normLeOne_frontier_lipschitz_cover*` terminals, of which this is an internal feeder), not named
after a person/place, introduces no structure. The `PROJECT_OVERVIEW.md` likewise lists the
public terminals, not this lemma, as the upstream exports. (Literature width was EXHAUSTIVE
regardless — see Phase 3.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def` — one-line check **n/a** (the body is a ~25-line proof in any case).

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | boundary covered by finitely many Lipschitz images of unit cube lattice point counting Davenport       | yes  | "boundary parametrized by finitely many Lipschitz maps `[0,1]^{n-1}→ℝ^n`" | the classical Lipschitz counting principle (Davenport); maps the cube into the codomain |
|  2 | WebSearch (general / named form) | Lipschitz parametrizable boundary counting lattice points Widmer Lang number field fundamental domain  | yes  | Widmer's `Lip(n,M,L)` class; Thm used for fundamental domains in number fields | Widmer, Lang GTM110 Ch VI, Schanuel, Masser–Vaaler — exactly the cited lineage |
|  3 | WebSearch (named-after / aliases)| Davenport lemma lattice points boundary parametrized M maps Lipschitz constant `"Lip(n"`                | yes  | `S ∈ Lip(D,M,L)`: `S⊆ℝ^D`, `M` maps, Lipschitz cover | "principle of Lipschitz" (Davenport 1951); class notation `Lip(n,M,L)` is Widmer's |
|  4 | **PDF verbatim** (Widmer AMS)    | `pdftotext` of Widmer, *Lipschitz class, narrow class, and counting lattice points*, Proc. AMS 140 (2012) | **yes** | **Definition 2 + Thm 2.2 extracted verbatim** (quoted below) | the decisive source — gives the exact standard definition and the counting theorem |
|  5 | ChatGPT MCP                      | name + standard generality of "frontier covered by finitely many cube-Lipschitz maps"; is the cover general or per-set? | **DOWN** | Codex MCP failed (env note: MCP down) — fell back to WebSearch + verbatim PDF | recorded as attempted-but-unavailable |
|  6 | Local references                 | grep `.mathlib-quality/references/` ; `refs/Chebotarev/`                                                | n/a  | neither directory present          | only `overview/` exists under `.mathlib-quality/`; `refs/` absent — recorded n/a |
|  7 | nLab                             | rectifiable set / Lipschitz parametrization / geometry-of-numbers counting principle                   | yes  | rectifiable = covered by a Lipschitz image of a subset of ℝ^k; lattice counting error ∝ perimeter | gives the ambient notion (rectifiable/Lipschitz image) + confirms the counting principle |
|  8 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not a categorical concept          | point-set/metric geometry of a specific NT cone; no categorical content |
|  9 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept  | analytic / measure-geometry of the Minkowski cone; not scheme-theoretic |
| 10 | MathOverflow / Math.StackExchange| (folded into #1–#3) Lipschitz parametrizability of fundamental-domain boundary                          | partial | confirms it is the *standard input condition*, verified ad hoc per set | the cover is always proved per-set; only the counting consequence is general |
| 11 | recent arXiv (last 5 years)      | Lipschitz/o-minimal boundary lattice point counting; sharp o-minimality (2503.01731); heights & morphisms (2411.13522) | yes  | modern refinements still phrase the input as a `Lip(n,M,L)`/o-minimal boundary condition; the cover is verified per family of sets | confirms no general "cover producer" theorem; o-minimality is the modern competing input |

Protocol pass: WebSearch ran ≥3 queries at different generality levels (#1 specific principle, #2
named/general Widmer–Lang form, #3 named-after Davenport + class notation) ✓; ChatGPT MCP attempted
but **environment-down** (recorded, fell back to verbatim PDF) ✓; local refs checked (both absent
→ n/a) ✓; nLab checked ✓; Stacks/nCatLab n/a with reason ✓; MO folded in + arXiv (last-5-yr)
checked ✓.

### Verbatim standard definition (Widmer, Proc. AMS 140 (2012), Definition 2 — via `pdftotext`)

> **Definition 2.** "We say that a set S is in Lip(n, M, L) (or of Lipschitz class (n, M, L)) if S
> is a subset of Rⁿ, and if there are M maps φ₁, ..., φ_M : [0, 1]ⁿ⁻¹ ⟶ Rⁿ satisfying a Lipschitz
> condition (2.1) `|φᵢ(x) − φᵢ(y)| ≤ L|x − y|` for x, y ∈ [0, 1]ⁿ⁻¹, i = 1, ..., M, such that S is
> covered by the images of the maps φᵢ. We call L a Lipschitz constant for the maps φᵢ."

> **Theorem 2.2** (the *general counting* consequence). "Let Λ be a lattice in Rⁿ with successive
> minima λ₁, ..., λ_n. Let S be a bounded set in Rⁿ such that the boundary ∂S of S is in
> Lip(n, M, L). Then S is measurable and moreover [`|#(Λ∩S) − Vol S / det Λ| ≤ …` in terms of
> M, L, λᵢ]."

And the *per-set production* side (Widmer's own Thms 2.3, 2.4, and the ball case) each prove the
cover **ad hoc** for a specific family of sets ("∂S is in Lip(n, 1, 8n^{5/2}R)" for narrow class 1;
"∂S in Lip(2,1,2πsR)" for tight class in ℝ²; the polar-coordinate parameterization for spheres
`∂B_P(r)`). There is **no** general theorem in the literature that outputs a cover for an arbitrary
set — each region (ball, convex body, fundamental domain) gets its own boundary parametrization.

### Literature summary (Phase 3)

Concept identified as: **"boundary in the Lipschitz class `Lip(n, M, L)`"** — equivalently
"Lipschitz-parametrizable boundary", the input condition of Davenport's *principle of Lipschitz*
(1951) as crystallized by Schmidt and Widmer. Our theorem (with its `exists_lipschitzWith_…`
companion) is precisely "`∂(normAtAllPlaces '' normLeOne K)` is in `Lip(r, m, L)`".

Sources agree on the standard form: **yes** — Widmer's Definition 2 is the canonical statement and
matches the Lean form essentially symbol-for-symbol (M maps `[0,1]^{n-1} → ℝ^n`, common Lipschitz
constant, images cover the set). Gun–Ramaré–Sivaraman §3.3 (the project's cited source), Lang
GTM 110, and Debaene all use exactly this condition.

Most general standard form: there are **two distinct theorems** in the literature and they must not
be conflated:
- **(A) the counting theorem** — "boundary ∈ Lip(n,M,L) ⟹ `#(Λ∩S) = Vol/det + O(error)`" (Widmer
  Thm 2.2, Davenport's principle). This is **general and reusable**: it is stated for an *arbitrary*
  bounded set whose boundary is in the Lipschitz class.
- **(B) the cover-production theorem** — "for *this specific* S, exhibit the M maps and the
  constant L". This is **always ad hoc per set** (Widmer Thms 2.3/2.4, the sphere case; here the
  number-field cone).

Generality dimensions where the literature varies:
- **the codomain**: stated over `ℝⁿ` with the Euclidean norm. Our `realSpace K = (InfinitePlace K → ℝ)`
  is exactly such an `ℝⁿ` (`n = r`). No more-general normed-space version is standard — the lattice
  lives in `ℝⁿ`.
- **the domain of the maps**: universally `[0,1]^{n-1}` (the unit cube) — matching `Icc 0 1` here.
- **(B) is irreducibly set-specific**: there is no literature theorem producing a cover for a
  *general* set; the modern alternative input (o-minimality, e.g. arXiv 2503.01731) is a *different*
  condition, not a generalization that would absorb this per-set construction.

Disagreement with the literature: **none**. The theorem is a faithful, correctly-phrased instance
of side (B) — the cover-production half of the standard machinery — for the number-field cone
region, with the cube domain and common Lipschitz constant exactly as Widmer's Definition 2 demands.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): side (B) is *inherently* set-specific. The relevant
"standard form" to compare against is therefore not a more-general statement of *this* inclusion
(there is none), but the question of whether the **set** `normAtAllPlaces '' normLeOne K` and the
**construction** `frontierCoverFamily` are themselves number-field-specific or instances of
something mathlib should carry in general.

### Generality status table — `Chebotarev.frontier_subset_frontierCoverFamily`

| # | Parameter / ingredient                       | Current Lean form                                   | Literature-standard form                                  | Weaker / more general form exists? | Reason |
|---|----------------------------------------------|-----------------------------------------------------|------------------------------------------------------------|------------------------------------|--------|
| 1 | the set `normAtAllPlaces '' normLeOne K`     | the specific number-field norm-`≤1` cone image      | "a bounded set S" in the *counting* theorem; but the *cover* theorem is per-set | **NO** | the entire proof is about `expMapBasis`/`paramSet`/the box-boundary face structure of *this* cone; nothing carries to an arbitrary set |
| 2 | the cover family `frontierCoverFamily K`     | the explicit zero/`w₀`-face/side-face family        | "M maps `φᵢ`" — the maps are always exhibited per set       | **NO** | the faces `faceMapZero`/`faceMapSide` are built from `expMapBasis` and the `w₀`-distinguished place; they have no meaning off this cone |
| 3 | the cube domain `Icc 0 1` (`[0,1]^{r-1}`)    | unit cube, matching Widmer Def 2                    | `[0,1]^{n-1}` (universal)                                   | NO (already the standard)          | this *is* the standard domain |
| 4 | the codomain `realSpace K`                    | `(InfinitePlace K → ℝ) ≅ ℝ^r`                        | `ℝ^n`                                                       | NO (already the standard)          | already a finite-dim real coordinate space; the lattice lives here |
| 5 | `[NumberField K]`, `[Field K]`               | number-field instances                              | n/a (the *set* is number-field-defined)                    | **NO** | the set itself only exists for a number field; removing the instances removes the statement |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *for what it is* — an irreducibly set-specific
cover-production statement (side B). Every "parameter" that could be weakened (codomain, cube
domain) is **already** at the literature-standard generality; the rest (the set, the face family,
the `NumberField` instances) cannot be weakened **because they constitute the very content** — the
theorem is *about* the boundary of this one number-field region. There is no strictly-more-general
true statement of this inclusion; the only more-general object in the area is the *counting*
theorem (Phase 5), which is a **different** result that this theorem feeds.

Number of weakening opportunities found: **0**.
Cost of restatement: n/a (no restatement available — generalizing the *set* would change the
theorem into a false or vacuous claim).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                               | no       | already fully typeclass-driven (`[NumberField K]`) | — |
|  2 | sequences/metric → filters/topological?                                                           | no       | `frontier`/`closure`/`image`/`⋃` are already the topological primitives; `LipschitzWith` (companion) is the bundled metric notion mathlib already uses | — |
|  3 | construct an object → universal-property class?                                                   | no       | the cover family is a genuine explicit construction; the *counting* theorem already abstracts the condition to a `∃`-hypothesis (`hlip`) — the modern packaging is **already done** in `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                | no       | sets are genuine ad-hoc subsets of `realSpace`, not substructures | — |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                                          | no       | `realSpace K` is already the minimal coordinate space; the lattice/counting genuinely needs `ℝ^r` | — |
|  6 | 1-categorical → higher-categorical?                                                               | no       | n/a | — |
|  7 | concrete index → arbitrary algebraic structure?                                                  | no       | the index `Unit ⊕ Unit ⊕ (…×Bool)` enumerates the *faces of this specific box*; it is not a numeric index to be generalized | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The result is a concrete pointwise set-inclusion for one
number-field region. The one genuine "modernisation" in this area — abstracting the Lipschitz-cover
condition into a reusable `∃ m M φ, (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Icc 0 1`
hypothesis over an arbitrary `s` — has **already been performed** in the sibling
`exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (LatticePointCount.lean:366), which is the
Lean form of Widmer's Theorem 2.2. `frontier_subset_frontierCoverFamily` is the *consumer-side
witness* that this very hypothesis holds for `normAtAllPlaces '' normLeOne K`; there is nothing
left to modernise on the witness itself.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.frontier_subset_frontierCoverFamily`

[A] Lean-Finder       (MCP unavailable in this env)                                  n/a: index tool not wired in
[B] Loogle            `frontier _ ⊆ iUnion (fun _ => _ '' Icc 0 1)` ; `frontier (_ '' _) ⊆ _`   no relevant hits; see grep [D]
[C] LeanSearch        (MCP unavailable in this env)                                  n/a: index tool not wired in
[D] Grep mathlib src  `frontier.*⊆.*''.*Icc`, `frontier.*⊆.*iUnion`, `LipschitzWith.*frontier`, `frontier (normLeOne`, `frontier.*normAtAllPlaces`, `Lip.*class`, `frontier.*Lipschitz`  results below
[E] Name pattern      `frontier_subset_frontierCoverFamily`, `frontierCoverFamily`, `normLeOne`, `normAtAllPlaces`   resolved (project decl; mathlib stops at the *measure* result)

Grep [D] results (mathlib pin `d90090f`):
- `frontier .* ⊆ .* '' Icc` → **empty**. `frontier .* ⊆ .* iUnion` → **empty**. No Lipschitz-cover
  / `Lip(n,M,L)`-style boundary infrastructure anywhere in mathlib.
- `frontier (normLeOne …)` / `frontier .* normAtAllPlaces` → the **only** hit is
  `volume_frontier_normLeOne : volume (frontier (normLeOne K)) = 0`
  (`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:868`). Mathlib proves the
  frontier is **measure-zero** and stops there — it never states any *pointwise* cover of the
  frontier, let alone a Lipschitz one.
- `Mathlib/Algebra/Module/ZLattice/Covolume.lean` has `ZLattice.covolume` and covolume-as-determinant
  lemmas, but **no error-term / lattice-point-counting-with-Lipschitz-boundary** machinery at all.
- `tendsto_card_div_pow_atTop_volume` and friends (`Analysis/BoxIntegral/UnitPartition.lean`,
  `NumberTheory/NumberField/Ideal/Asymptotics.lean`) give the **rate-free** limit
  `card / nᵈ → vol s` — the *qualitative* counting result. Mathlib has **no effective (with-error)
  version**, hence no consumer that would need a Lipschitz cover.

Mathlib ingredients that the proof *does* reuse (all present): `normAtAllPlaces_normLeOne_eq_image`
(NormLeOne.lean:655), `expMapBasis`/`paramSet`/`injective_expMapBasis`/`compactSet_eq_union`
(the `frontier_image_paramSet_subset` inputs), plus generic `Set.image`/`frontier`/`iUnion` algebra.

Searched for both:
  - the user's current form (`frontierCoverFamily`/`normLeOne` pointwise cover) — **not in mathlib**.
  - the literature-standard form (any `Lip(n,M,L)` boundary-cover, for *this* or *any* set) —
    **not in mathlib** (no Lipschitz-boundary-class infrastructure exists; only the measure-zero
    frontier result and the rate-free counting limit are present).

Concluded: **not in mathlib** (neither the specific `normLeOne`-frontier Lipschitz cover nor any
general Lipschitz-boundary-class machinery exists; mathlib stops at `volume_frontier_normLeOne` and
the rate-free `tendsto_card_div_pow_atTop_volume`). This theorem genuinely fills a gap — but the gap
is the *effective-lattice-count program* of which this is the per-set boundary input.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `Chebotarev.frontier_subset_frontierCoverFamily`

Internal use count: **2** (within the project, excluding the declaring line).
External-to-file callers: **0 distinct files** — both uses are in the *same* file
(`ForMathlib/NormLeOneLipschitz.lean`).

| Caller file:line                                              | Usage pattern (one-line excerpt)                               |
|--------------------------------------------------------------|----------------------------------------------------------------|
| ForMathlib/NormLeOneLipschitz.lean:358                       | `exact frontier_subset_frontierCoverFamily K`  (closes `normLeOne_frontier_lipschitz_cover`, the realSpace public terminal) |
| ForMathlib/NormLeOneLipschitz.lean:610                       | `refine (Set.preimage_mono (frontier_subset_frontierCoverFamily K)).trans ?_`  (feeds the `mixedSpace`/`index` cover transport) |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?): **none** — no
other site reconstructs `frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ …`. The downstream consumers
of the *whole pipeline* (`ZetaProduct.lean`, `IdealCongruenceCount.lean`) call the public terminals
`normLeOne_frontier_lipschitz_cover` / `…_index`, not this internal lemma.

Call-sites reading: K = 2 internal uses, both feeding the file's public `…_lipschitz_cover*`
terminals; no external consumers; no inline re-derivation. By the Phase-6 signal table this is a
genuine **named intermediate in a published-API pipeline** (it is the load-bearing inclusion behind
all three terminals), not dead code and not a one-shot wrapper that consumers bypass. It supports a
YES-family disposition for the *pipeline*, but — being the bespoke per-set witness — it argues for
upstreaming *with* its terminals, not as a standalone general lemma.

### Composition check (Phase 6)

Can `frontier_subset_frontierCoverFamily` be derived from mathlib in ≤3 chained calls?

Attempt 1: chain mathlib's `volume_frontier_normLeOne` / `normAtAllPlaces_normLeOne_eq_image` with a
generic frontier-cover lemma.
  - Mathlib decls available: `normAtAllPlaces_normLeOne_eq_image`, `volume_frontier_normLeOne`.
  - Result: **fails**. `volume_frontier_normLeOne` is a *measure* statement and yields **no**
    pointwise cover. There is no mathlib lemma taking a set to a Lipschitz cube-cover of its frontier
    (Phase 5: none exists). The rewrite `normAtAllPlaces_normLeOne_eq_image` is just step 1 of the
    real proof.

Attempt 2: compose the three project lemmas `frontier_image_paramSet_subset`,
`image_boundary_subset_faces`, `exists_cubeRelabel_eq`.
  - Result: **this is the actual ~25-line proof**, and it composes *project* lemmas, not mathlib
    primitives. Two of the three feeders (`frontier_image_paramSet_subset`,
    `image_boundary_subset_faces`) are themselves non-trivial project results (each already assessed
    YES-but-generalise / project-specific). Plus the per-piece `clampUnit_eq_self` /
    `exists_cubeRelabel_eq` matching with `rintro`/`obtain`/`change`/`rw` — genuine set-algebra
    reasoning, not a `.trans`/`.symm`/single-application chain.

Conclusion: **NOT-COMPOSABLE** from mathlib in ≤3 calls. The proof is a real (if elementary)
multi-step argument that assembles three bespoke project lemmas with per-face set-algebra; mathlib
supplies none of the boundary-cover content.

---

## Verdict: `Chebotarev.frontier_subset_frontierCoverFamily`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the result is the **cover-production half** (side B) of the standard
  "boundary in Lipschitz class `Lip(n,M,L)`" machinery (Davenport's principle / Widmer Def 2,
  extracted verbatim; Gun–Ramaré–Sivaraman §3.3, Lang GTM 110, Debaene). Side B is **irreducibly
  set-specific** in the literature — every region proves its own cover. Our form matches Widmer's
  Definition 2 symbol-for-symbol (M maps `[0,1]^{r-1} → ℝ^r`, common Lipschitz constant, images
  cover the boundary).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL for what it is** — 0 weakening opportunities;
  every generalizable slot (cube domain, `ℝ^r` codomain) is already at the standard generality, and
  the set / face family / `NumberField` instances *are* the content. Modern-idiom: the only
  abstraction move (a reusable `∃`-cover hypothesis over arbitrary `s`) is **already** realised in
  the sibling counting theorem; nothing left to modernise on the witness.
- Mathlib search (Phase 5): **not in mathlib** in either form — mathlib stops at the measure-zero
  `volume_frontier_normLeOne` and the rate-free `tendsto_card_div_pow_atTop_volume`; it has **no**
  Lipschitz-boundary-class infrastructure and **no** effective (with-error) lattice count.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib in ≤3 calls (≈25-line proof gluing
  three bespoke project lemmas with per-face set-algebra; mathlib supplies none of the cover
  content). K = 2 internal uses feeding the file's public terminals; no external callers; no inline
  re-derivation.

**Rationale:**

This is *not* a NO verdict: the result is genuinely absent from mathlib (Phase 5), it correctly
realises a standard and well-attested condition (Widmer's `Lip(n,M,L)` boundary class, Phase 3), it
is at the right generality (Phase 4: 0 weakenings), and it does not compose from mathlib primitives
(Phase 6). But it is also *not* a clean `YES-add-as-is`, for two reasons the skill cannot resolve
alone, both turning on mathlib **policy** rather than mathematics:

(1) **Standalone vs. bundled.** `frontier_subset_frontierCoverFamily` is the *cover-inclusion* half
of a two-part fact; the *common-Lipschitz-constant* half is the separate
`exists_lipschitzWith_frontierCoverFamily`, and the mathematically meaningful, citable statement is
their conjunction — and indeed the file's own *public terminal*
`normLeOne_frontier_lipschitz_cover` (line 348) is exactly that bundled `∃ m M φ, (∀ j, LipschitzWith
M (φ j)) ∧ frontier … ⊆ ⋃ j, φ j '' Icc 0 1`. So this lemma is almost certainly an **internal
feeder** that should be upstreamed (if at all) *inside* the bundled terminal and the `frontierCoverFamily`
/ `faceMap*` construction, not as a standalone export. Whether mathlib wants the disassembled
inclusion as its own public lemma, or only the bundled terminal, is a librarian's call.

(2) **Does this whole pipeline belong in mathlib at all, and where?** The cover exists *only* to
discharge the `hlip` hypothesis of the **effective** lattice-point count
`exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (Widmer's Thm 2.2 in Lean). Mathlib currently
has the *qualitative* count (`tendsto_card_div_pow_atTop_volume`) but **not** the effective version,
and it proves only the *measure-zero* frontier (`volume_frontier_normLeOne`), not a pointwise
Lipschitz cover. So upstreaming this lemma in isolation would leave it **without a mathlib consumer**
— the effective count it feeds is itself still a project result (`ForMathlib/LatticePointCount.lean`).
The natural home is mathlib's own `NormLeOne.lean` (as the pointwise companion to
`volume_frontier_normLeOne`) **iff** the effective-count program lands too; absent that program, this
is an orphan. That sequencing/ownership decision (ship the whole effective-count program, of which
this is the boundary input; or hold it project-local until mathlib wants the program) is a human
call, not a per-decl one.

Cost is **not** invoked anywhere in this rationale (the proof is cheap); the BORDERLINE is purely the
two policy questions above. Per the gate, "cost too high" would be an illegitimate downgrade — that
is not what is happening here.

  Numbered questions (for the human):
    1. Should the upstreaming unit be the **bundled terminal** `normLeOne_frontier_lipschitz_cover`
       (with `frontierCoverFamily`, `faceMap*`, and *this* inclusion as private/internal lemmas),
       rather than this disassembled cover-inclusion as a standalone public lemma? (Expected: yes.)
    2. Does mathlib want this at all **before** the effective lattice-point count
       `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (Widmer Thm 2.2) is upstreamed — i.e.
       should the whole effective-count program go up as one body of work, with this as its
       `normLeOne` boundary input, or stay project-local until then?
    3. If upstreamed, is the right home mathlib's own
       `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`, as the pointwise
       Lipschitz-cover companion to `volume_frontier_normLeOne`? (Expected: yes.)

  Next action: the user answers (1)–(3) — most likely "bundle it, ship it with the effective-count
  program, home it in mathlib's `NormLeOne.lean`". Then re-run `/mathlibable
  Chebotarev.normLeOne_frontier_lipschitz_cover` (the public terminal — the correct upstreaming
  grain) to drive the actual PR, with this lemma carried as an internal feeder.

---

## Next step

Answer the three numbered questions above (standalone-vs-bundled; ship-now-vs-with-the-effective-count
program; mathlib home). The likely resolution: this inclusion is an **internal feeder**, upstreamed
*inside* the bundled public terminal `normLeOne_frontier_lipschitz_cover` and the `frontierCoverFamily`
construction, homed in mathlib's `NormLeOne.lean` as the pointwise companion to
`volume_frontier_normLeOne`, and shipped together with the effective lattice-point count
(`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, = Widmer Thm 2.2) that consumes it — since
mathlib presently has only the rate-free count and the measure-zero frontier. Re-run `/mathlibable`
on that terminal to plan the PR.
