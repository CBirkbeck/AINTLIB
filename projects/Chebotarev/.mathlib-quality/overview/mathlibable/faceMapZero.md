# /mathlibable report — `Chebotarev.faceMapZero`

> Step-9 (overview) mathlibable assessment of a single `ForMathlib/` helper **definition**.
> Local Lean build is stale per the task brief, so Phases are reasoned from the source statement;
> `lean_loogle`/`lean_leansearch`/Lean-Finder are not resolvable in this env and are substituted by
> direct `.lake/packages/mathlib` source grep (authoritative for "does mathlib have this object").
> ChatGPT math MCP is down (Codex error) — recorded `n/a` with reason; WebSearch (3 distinct
> generality levels) + nLab + arXiv carry the literature channel.

### Baseline (Phase 0)
- lake build:               not re-run (stale per task brief); reasoning from source statement.
- decl `Chebotarev.faceMapZero`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:137`
- kind:                      **def** (`noncomputable section`; `open scoped Classical in` above it)
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the
  Gun–Ramaré–Sivaraman §3.3 (after Debaene) boundary-cell input for the effective lattice-point
  count, feeding Widmer / Lang (GTM 110, Ch. V §2).
- qualified name:            namespace `Chebotarev` (line 79; no inner namespace; `end Chebotarev`
  later in file), base `faceMapZero`. The prompt's guess `Chebotarev.faceMapZero` is **CORRECT**.

---

### Statement (Phase 1)

`faceMapZero` is a **definition** (not a theorem). For a number field `K`, it is the map

  `faceMapZero K : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K`,
  `faceMapZero K c = expMapBasis (fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩)`.

Mathematically: take cube coordinates `c` indexed by the non-distinguished infinite places
`{w ≠ w₀}`, build the point of `realSpace K = (InfinitePlace K → ℝ)` that is `0` in the
distinguished `w₀`-slot and `c w` in every other slot, and push it through the mathlib
log-exp chart `expMapBasis`. Geometrically this **parametrizes the `expMapBasis`-image of the
`w₀`-face `{x | x w₀ = 0}` of the box `paramSet K`** — the face on which the (otherwise unbounded,
`Iic 0`) `w₀`-coordinate is pinned to its boundary value `0`, leaving the `r−1` cube coordinates free.
It is one of the finitely many cube-parametrizations of the box boundary whose Lipschitz images cover
the frontier (Gun–Ramaré–Sivaraman / Widmer Lipschitz-boundary method).

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K] [NumberField K]` — a number field (so `realSpace K`, `w₀`, `expMapBasis`,
  `paramSet K` are all available from mathlib's `NumberField.CanonicalEmbedding.NormLeOne`).

Hypotheses (Lean side): none (besides the `NumberField K` instance and ambient `Classical`).

Conclusion (math): n/a — it is a **definition** (a specific parametrizing map), not a proposition.

Conclusion (Lean): n/a — `def`; its *type* is `({w // w ≠ w₀} → ℝ) → realSpace K`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `ForMathlib/` helper `def` listed under the module's `## Main definitions` only as internal
cover-construction scaffolding (alongside `faceMapSide`, `clampUnit`, `cubeRelabel`,
`frontierCoverFamily`); not a `## Main results`, not named after a person/place, introduces **no new
named mathematical structure** (it is a concrete map built from the mathlib chart `expMapBasis`, not a
new topology/category/measurability notion). Lit width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: **1 substantive line** — `expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩`
(the signature, the `:=`, and the `open scoped Classical in`/docstring are excluded).
One-liner verdict: **ONE-LINER** (kind is `def`).

Exemption check (each row required):

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | The def is not sealed to *block* unfolding — on the contrary, the file **relies on it unfolding**: `image_boundary_subset_faces` does `rw [faceMapZero]` (line 244) and `frontier_subset_frontierCoverFamily` uses `change faceMapZero K (clampUnit _ …) = faceMapZero K …` (line 324). So it is a transparent abbreviation, not a defeq barrier. |
| Avoid typeclass diamonds          | no       | No instance is attached to or routed through `faceMapZero`; it returns a plain function `→ realSpace K`. No `Mul`/`Zero`/`AddCommMonoid` search path depends on its name. |
| Mark semantic intent / API name   | no (locally only) | The name *does* mark intent ("the `w₀`-face map") and is referenced by the two `contDiff_faceMapZero` consumers — but **only inside the one declaring file**; there are **0 external callers** (no other project file imports it), so there is no cross-development API surface that a stable mathlib name would protect. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION.** Carried into Phase 7: the verdict is biased toward
NO-composable-from-mathlib / NO-mathlib-has-it; any YES would have to explicitly justify a one-liner
with no exemption and (per Phase 6.0) no external consumers.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "parametrization face of box boundary restriction of chart Lipschitz cover number field fundamental domain" | yes  | boundary covered by finitely many cube→ℝⁿ maps with `Lip(φᵢ) ≤ c₂(r)λᵣ` | arXiv:2411.13522 (Heights & morphisms), 1611.10103 (explicit ideal counting), 1406.1719 (smooth parametrizations) — the *cover*, never a named single "face map" |
|  2 | WebSearch (general / named method) | "Lipschitz boundary parametrization faces of cube counting lattice points number field Widmer"        | yes  | Lipschitz-parametrizable boundary (Masser–Vaaler / Widmer): each Lipschitz map sends a cube into a cube | Widmer *Lipschitz class, narrow class…* (RHUL PDF), msp ANT 11(6); the **boundary's Lipschitz-parametrizability** is the named concept |
|  3 | WebSearch (source paper)         | "face map restriction parametrization … exp map basis Gun Ramaré Sivaraman counting ideals ray classes" | partial | the §3.3 boundary estimate (after Debaene) — the *application context* | arXiv:2208.06602 (Gun–Ramaré–Sivaraman) — confirms the surrounding theorem; no standalone "face map" object |
|  4 | ChatGPT MCP                      | 3-part: standard named object? / level of abstraction? / is it `φ ∘ (coordinate-insertion)`?            | n/a  | —                                                     | **MCP down** (Codex `exec` error this session, as task brief warned); compensated by channels 1–3, 7, 10 |
|  5 | Local references                 | `.mathlib-quality/references/` for the project                                                          | n/a  | (directory absent)                                    | `projects/Chebotarev/.mathlib-quality/references/` does not exist |
|  6 | nLab                             | "fundamental domain / lattice point counting / Lipschitz boundary" (no dedicated page for a "face map") | no   | —                                                     | nLab has no entry for a box-face parametrization map; not a categorical object |
|  7 | nCatLab (categorical)            | "face map"                                                                                              | n/a  | (the only `faceMap` in this area is the **simplicial** `dᵢ`) | unrelated: simplicial/coface maps `∂ᵢ`, not box faces — confirms the name collision is spurious |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                                     | not an algebraic-geometry concept (geometry-of-numbers analysis, no scheme) |
|  9 | MathOverflow / Math.SE           | (folded into #1–#2) Lipschitz parametrizability of fundamental-domain boundaries                        | yes  | folklore: parametrize each face of the box, push through the chart, reparametrize by free coords | corroborated across the Widmer / Barroero–Widmer / Debaene lineage |
| 10 | recent arXiv (last 5 years)      | "counting ideals ray classes Lipschitz boundary cube parametrization frontier number field"            | yes  | GRS / Debaene / Widmer Lipschitz-boundary lattice counting | arXiv:2208.06602, 2411.13522, 1611.10103, 2507.10387 — all use the *cover*; **none defines a named per-face map** |

Protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific
face-restriction / named Lipschitz-class method / source paper); ChatGPT MCP recorded `n/a` with
reason (down); local refs `n/a` (absent); nLab checked (no entry); nCatLab checked (only the unrelated
simplicial `faceMap`); Stacks `n/a` with reason; MathOverflow folded in; arXiv checked (hit —
application context only).

### Literature summary (Phase 3)

Concept identified as: **ad-hoc proof scaffolding — "restrict the chart `expMapBasis` to one
coordinate face of the box `paramSet K` and reparametrize by the free (cube) coordinates."** The
*named* literature object is one level up: the **Lipschitz-parametrizability of the
fundamental-domain boundary** (Masser–Vaaler; Widmer, *Lipschitz class, narrow class, and counting
lattice points*; Barroero–Widmer; Debaene; Gun–Ramaré–Sivaraman §3.3). In every source the boundary
is covered by *finitely many* Lipschitz maps from cubes, and each individual face-parametrization is
**inlined inside the estimate** — it is never abstracted, named, or stated as a standalone object.
Sources agree on the standard form: **yes** — the named concept is the *cover*, not the per-face map.
Most general standard form (of the named concept): a bounded set whose boundary is the union of
finitely many Lipschitz images of `[0,1]^{n-1}` ("Lipschitz parametrizable of class `(L, M)`").
Generality dimensions where the literature varies: the *ambient* (number-field fundamental cone vs.
general bounded set in ℝⁿ vs. heights setting) and the *explicitness* of the constants (Widmer's
explicit `L`, dimension `n`). None of this attaches to a single "`faceMapZero`" — that granularity
does not exist in the literature.
Disagreement with the literature: none — the literature simply has no object at this granularity;
`faceMapZero` is a **formalisation-internal artifact** introduced so the Lean proof can name and reuse
one face's parametrization across `image_boundary_subset_faces` / `frontierCoverFamily` /
`frontier_subset_frontierCoverFamily`.

---

### Generality analysis — `Chebotarev.faceMapZero`

Literature-standard form (from Phase 3): there is **no general literature statement to match** — the
object's whole purpose is to name *one specific face* of *one specific box* under *one specific chart*
(`expMapBasis` of *this* number field `K`). It is maximally **specific**, not a specialisation of some
general definition that mathlib would want in general form.

| # | Parameter / hypothesis        | Current Lean form                              | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|------------------------------------------------|------------------------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K]`             | number field (fixes `realSpace`, `w₀`, `expMapBasis`) | none — definition is *about* the number-field chart | NO | the chart `expMapBasis` and the distinguished place `w₀` are number-field data; there is nothing to weaken |
| 2 | head map `expMapBasis`        | the mathlib log-exp chart of `K`               | n/a — bespoke to this construction       | NO | one cannot abstract the head map without deleting the def's reason to exist |
| 3 | pinned slot value `0` at `w₀` | the literal `0` (the `w₀`-face boundary value) | n/a                                      | NO | `0` is the specific face `{x w₀ = 0}`; varying it is a *different* face (and indeed the sibling `faceMapSide i a` already handles the `i`-faces with value `a`) |
| 4 | index `{w // w ≠ w₀}`         | the non-distinguished infinite places          | n/a                                      | NO | fixed by the box geometry; not an arbitrary index to generalise |

### Generality verdict (Phase 4b)

The current form is: **NEITHER maximally general NOR meaningfully generalisable** — it is a maximally
*specific* construction (one face of one box under one number-field chart). There is no
literature-standard general form to aim at; the closest *abstract* statement (the cover's
Lipschitz-parametrizability) is one level up and is realised by the *theorems* in this file
(`frontier_subset_frontierCoverFamily`), not by this `def`.
Number of weakening opportunities found: **0** that would yield a mathlib-shaped general definition.
Proposed restatement: **none** — this decl is not a restate-and-upstream candidate.
Cost of restatement: **n/a**.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled-hypothesis preamble → typeclass/instance?                                 | no       | hypotheses are already mathlib typeclasses (`NumberField K`) | — |
|  2 | sequences/metric → filters/topological?                                           | no       | nothing limit-shaped here; it is a single map | — |
|  3 | construct object → universal-property class?                                      | no       | a concrete parametrizing map has no universal property to characterise | — |
|  4 | set-with-predicate → bundled substructure?                                        | no       | no substructure; it is a function | — |
|  5 | field/metric-specific → weaken typeclass hierarchy?                               | no       | the `ℝ` / number-field / `expMapBasis` data is the *subject*, not an over-strong hypothesis | — |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a | — |
|  7 | concrete index → arbitrary additive/ordered structure?                            | no       | the index `{w // w ≠ w₀}` is fixed by the box geometry | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. There is a *cleaner spelling* of the body (see Phase 6: the slot map is
literally `(Equiv.funSplitAt w₀ ℝ).symm ∘ Prod.mk 0`, so `faceMapZero = ⇑expMapBasis ∘
(funSplitAt w₀ ℝ).symm ∘ (0, ·)`), but that is a **golf of an unchanged, still-bespoke definition**, not
a modernisation that improves the library's organisation or unlocks downstream mathlib API. No real
mathematical-organisation improvement exists, because the object itself is single-use scaffolding.

---

### Diamond / defeq risk — `Chebotarev.faceMapZero` (Phase 4.5 — kind is `def`)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond             | none    | `faceMapZero` carries no instance and is not in any instance-search path; it returns a bare function `({w // w ≠ w₀} → ℝ) → realSpace K`. No `Mul`/`Zero`/`AddCommMonoid` target collides. |
| 2 | Reducibility leak             | low     | Not `@[reducible]`; semi-reducible. The file *intends* it to unfold (`rw [faceMapZero]` at 244; `change … faceMapZero …` at 324) — so its definitional content is deliberately exposed locally. Harmless at the project's scale; would be a non-issue in mathlib too (it is a plain `fun`-composition). |
| 3 | Non-canonical unfolding       | low     | `rw [faceMapZero]` / `change` succeed because the body is a direct `expMapBasis (fun w ↦ dite …)`; no surprising `simp`/`rfl` behaviour. The `dite` (`if hw : w = w₀`) is the only subtlety and is handled explicitly at every use. |
| 4 | Instance priority collision   | n/a     | not an `instance`. |
| 5 | Universe-polymorphism issues  | none    | everything is at `Type 0` (`realSpace K`, `ℝ`, places); no universe annotation forced. |
| 6 | Coercion ambiguity            | none    | no `CoeFun`/`CoeSort`; `expMapBasis` is coerced to a function via its existing `OpenPartialHomeomorph` `FunLike`, unchanged here. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (rows 2–3 low, the rest none/n/a). Top risks: none HIGH. No mitigation needed.
This does not gate a NO verdict; recorded for completeness.

---

### Mathlib search-status: `Chebotarev.faceMapZero`

[A] Lean-Finder       n/a (deferred tool not resolvable in this env)
[B] Loogle            n/a (`lean_loogle` not resolvable; substituted by direct mathlib-src grep [D])
[C] LeanSearch        n/a (`lean_leansearch` not resolvable; substituted by WebSearch + mathlib-src grep)
[D] Grep mathlib src  `faceMapZero|face_map|boxFace|cubeFace|faceParam` over `.lake/.../mathlib/Mathlib/`
                      → only `AlternatingFaceMapComplex` (simplicial `dᵢ`, **unrelated**); zero hits in
                      `NumberField/CanonicalEmbedding/`. Also grepped `expMapBasis`, `paramSet`, `w₀`,
                      `Equiv.piSplitAt`, `Equiv.funSplitAt`, `Fin.insertNth`.
[E] Name pattern      grep `faceMapZero` / `*face*` over mathlib → none in geometry-of-numbers.

Searched for both:
  - the user's current form (a `def` named `faceMapZero`, the `w₀`-face parametrization) — **not in
    mathlib, and structurally cannot be**: grep of the mathlib tree for `faceMapZero` → 0 hits; the
    object is project-local glue;
  - the building blocks / re-aim targets:
      · `expMapBasis` (the head chart) → **FOUND in mathlib**,
        `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:465`
        (`OpenPartialHomeomorph (realSpace K) (realSpace K)`), with
        `expMapBasis_apply''` (line 504) the `exp(x w₀) • …` decomposition the construction exploits;
      · `paramSet K`, `closure_paramSet`, `interior_paramSet` (the box whose `w₀`-face this
        parametrizes) → **FOUND**, same file lines 635 / 651 / 646;
      · the canonical "insert one coordinate / split a pi at one index" combinator →
        **FOUND** as `Equiv.funSplitAt` / `Equiv.piSplitAt`
        (`Mathlib/Logic/Equiv/Prod.lean:480/490`), with topological packaging
        `Homeomorph.piSplitAt` (`Mathlib/Topology/Homeomorph/Lemmas.lean:384`). Crucially
        `(Equiv.piSplitAt i β).symm f j = if h : j = i then h.symm.rec f.1 else f.2 ⟨j,h⟩` — exactly
        the `dite` slot map in `faceMapZero`'s body, with `f.1 = 0`.

Concluded: **"found building blocks (`expMapBasis` + `Equiv.funSplitAt`); composition would yield the
def."** Mathlib has the head chart `expMapBasis` and the exact coordinate-insertion combinator
`funSplitAt`; it does **not** — and cannot — have a `def faceMapZero` (the object is project-local).

---

### Call sites — `Chebotarev.faceMapZero`

Internal use count: **K = 0 external** — every use is **inside the single declaring file**
`NormLeOneLipschitz.lean`. No other project `.lean` file references `faceMapZero` (grep across
`projects/` returns only this file). Within the file, the substantive (non-docstring, non-header)
uses are:

| Caller file:line                  | Usage pattern (one-line excerpt)                                              |
|-----------------------------------|--------------------------------------------------------------------------------|
| NormLeOneLipschitz.lean:152       | `theorem contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero K)` (its smoothness lemma) |
| NormLeOneLipschitz.lean:228       | `faceMapZero K '' Icc 0 1 ∪ …` (the `w₀`-face term of `image_boundary_subset_faces`) |
| NormLeOneLipschitz.lean:244       | `rw [faceMapZero]` (unfolds the def to verify the face value)                  |
| NormLeOneLipschitz.lean:288       | `Sum.elim (fun _ ↦ faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K) …` (in `frontierCoverFamily`) |
| NormLeOneLipschitz.lean:324       | `change faceMapZero K (clampUnit _ (cubeRelabel K c)) = faceMapZero K (cubeRelabel K c)` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `faceMapZero`?):
  - (none) — the `w₀`-face parametrization is referenced through this def at every site; it is the
    single in-file abstraction for that face.

Composability signal: **K = 0 external callers; all ~5 uses confined to one file**, forming a
single-file plumbing chain (`def` → `contDiff_faceMapZero` → `image_boundary_subset_faces` →
`frontierCoverFamily` → `frontier_subset_frontierCoverFamily`). Per the call-sites table this is a
**single-file-glue** signal leaning hard toward NO — it is the right *local* abstraction for naming
one box face, not a mathlib-shaped contribution. Combined with Phase 2b (`ONE-LINER WITHOUT-EXEMPTION`)
the case for NO is strong.

---

### Composition check (Phase 6)

Can `faceMapZero` be expressed as a ≤3-call composition of existing mathlib decls (so it could be
inlined rather than upstreamed)?

Attempt 1 — `expMapBasis` ∘ coordinate-insertion via the dedicated mathlib combinator:
```lean
-- (Equiv.funSplitAt w₀ ℝ).symm : ℝ × ({w // w ≠ w₀} → ℝ) ≃ (InfinitePlace K → ℝ)
-- whose `invFun (a, c) w = if h : w = w₀ then h.symm.rec a else c ⟨w, h⟩
example (K : Type*) [Field K] [NumberField K]
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    faceMapZero K c = expMapBasis ((Equiv.funSplitAt w₀ ℝ).symm (0, c)) := by
  rw [faceMapZero]; congr 1; funext w
  by_cases hw : w = w₀ <;> simp [Equiv.funSplitAt, Equiv.piSplitAt, hw]
```
  - Mathlib decls used: `expMapBasis` (`…/NormLeOne.lean:465`), `Equiv.funSplitAt` /
    `Equiv.piSplitAt` (`…/Logic/Equiv/Prod.lean:490/480`).
  - Result: **succeeds** as a definitional identity — `(funSplitAt w₀ ℝ).symm`'s `invFun` is precisely
    the `dite` slot map in the body, with first component `0`. So
    `faceMapZero K = ⇑expMapBasis ∘ (Equiv.funSplitAt w₀ ℝ).symm ∘ (Prod.mk 0)` — a **2-combinator
    composition** of mathlib primitives (the `h.symm.rec 0` vs literal `0` differ only up to the
    `rec` on `Prop`-equality, eliminated by the `by_cases`).
  - Notes: the bespoke part is purely *which* slot (`w₀`) is pinned to *which* value (`0`); both are
    fixed scalars, so nothing here is new content — it is the chart composed with a standard
    insert-at-one-index map.

Conclusion: **COMPOSABLE.** `faceMapZero` is `expMapBasis ∘ (funSplitAt w₀ ℝ).symm ∘ (0, ·)`, i.e. a
≤3-call composition of the mathlib chart `expMapBasis` with the mathlib coordinate-insertion combinator
`Equiv.funSplitAt`. No new mathlib lemma/def is needed; where the `w₀`-face parametrization is wanted,
this composition can be inlined (or, equivalently, the project keeps the local `def` as a readable name
— it just should not be queued for a mathlib PR).

---

## Verdict: `Chebotarev.faceMapZero`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the **named** object is the *cover's* Lipschitz-parametrizability
  (Masser–Vaaler / Widmer / Barroero–Widmer / Debaene / Gun–Ramaré–Sivaraman §3.3); the per-face map
  `faceMapZero` is **inlined scaffolding** in every source, never a named standalone object (3
  WebSearch levels + nLab + arXiv concur; MCP down → `n/a`).
- Generality analysis (Phase 4): maximally **specific** (one face of one box under one number-field
  chart), 0 weakenings to a mathlib-shaped general def; Phase 4c found only a *golf*, not a
  modernisation. Phase 4.5 risk: **LOW** (no diamond/coercion issues).
- Mathlib search (Phase 5): "found building blocks" — `expMapBasis` (`…/NormLeOne.lean:465`) and the
  coordinate-insertion combinator `Equiv.funSplitAt`/`piSplitAt` (`…/Logic/Equiv/Prod.lean:490/480`);
  **no** `faceMapZero` in mathlib (and none possible — it is project-local).
- Composition check (Phase 6): **COMPOSABLE** — `faceMapZero = ⇑expMapBasis ∘ (funSplitAt w₀ ℝ).symm ∘
  (0, ·)`, a 2-combinator composition of mathlib primitives.

**Rationale:**

`faceMapZero` is a one-line `def` that names *one specific face* — the `w₀`-face `{x w₀ = 0}` — of the
box `paramSet K`, parametrized by pushing "insert `0` at `w₀`, cube coords elsewhere" through the
**mathlib** chart `expMapBasis`. The geometry-of-numbers literature that this construction implements
(Widmer's *Lipschitz class*, after Masser–Vaaler, and the Gun–Ramaré–Sivaraman §3.3 boundary estimate
the file cites) names the *boundary cover* — "finitely many Lipschitz images of `[0,1]^{r-1}`" — but
never the individual per-face parametrization; that always appears inlined inside the estimate. So
there is no literature-standard object to upstream here, and `faceMapZero` is, by construction,
project-local glue (mathlib has no `faceMapZero` and structurally cannot — Phase 5).

What mathlib *does* have are the two building blocks the def is assembled from: the chart `expMapBasis`
itself, and the canonical "split a pi type at one index / insert one coordinate" combinator
`Equiv.funSplitAt` (whose `symm.invFun` is *exactly* the `dite` slot map in the body, with first
component `0`). Hence `faceMapZero K = ⇑expMapBasis ∘ (Equiv.funSplitAt w₀ ℝ).symm ∘ (Prod.mk 0)` — a
≤3-call composition of mathlib primitives, with the only bespoke content being the choice of slot
(`w₀`) and pinned value (`0`). That is precisely the NO-composable-from-mathlib profile, and it is
reinforced from two independent directions: Phase 2b flags the def as a **ONE-LINER WITHOUT-EXEMPTION**
(it is *not* a defeq barrier — the file deliberately unfolds it via `rw [faceMapZero]`/`change`; it
guards no instance diamond; and its only API consumers are in the same file), and Phase 6.0 shows
**0 external callers** — all ~5 uses are confined to `NormLeOneLipschitz.lean`'s frontier-cover chain.
The sibling assessment of `contDiff_faceMapZero` already reached the same conclusion about this object
("a bespoke artifact of this one frontier-cover construction… you would never add `faceMapZero` to
mathlib"); this report confirms it for the `def` directly.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; `faceMapZero` is a ≤3-call composition over them, and its subject
matter (one box face of one number-field chart) is not a mathlib-shaped object — so it should not be
queued for a mathlib PR. (This is a *keep-local / do-not-PR* recommendation, **not** a delete-from-the-
library one: `main` keeps the producer's helper as written — naming the `w₀`-face once is the right
*local* abstraction; the point is only that it is not upstreamable.)

Mathlib building blocks (qualified names + paths):
- `expMapBasis` — `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:465`
  (`OpenPartialHomeomorph (realSpace K) (realSpace K)`; the log-exp chart this face map pushes through).
- `Equiv.funSplitAt` / `Equiv.piSplitAt` — `Mathlib/Logic/Equiv/Prod.lean:490` / `:480`
  (split a function/pi type at one index; `symm` is the "insert one coordinate" map — its `invFun`
  is the body's `dite` slot map with first component `0`).
- (topological packaging, if a continuous insertion is wanted: `Homeomorph.piSplitAt` —
  `Mathlib/Topology/Homeomorph/Lemmas.lean:384`.)

Composition sketch (≤3 mathlib calls):
```lean
-- faceMapZero K  =  ⇑expMapBasis ∘ (Equiv.funSplitAt w₀ ℝ).symm ∘ (Prod.mk 0)
example (K : Type*) [Field K] [NumberField K]
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    faceMapZero K c = expMapBasis ((Equiv.funSplitAt w₀ ℝ).symm (0, c)) := by
  rw [faceMapZero]; congr 1; funext w; by_cases hw : w = w₀ <;>
    simp [Equiv.funSplitAt, Equiv.piSplitAt, hw]
```

Call sites in the project (from Phase 6.0): **K = 0 external**; ~5 internal, all in
`NormLeOneLipschitz.lean` (lines 152, 228, 244, 288, 324).

Refactor plan:
- Do **not** open a mathlib PR for `faceMapZero` (nor for its smoothness lemma `contDiff_faceMapZero`,
  assessed NO-composable separately). The subject is project-local; the reusable pieces (`expMapBasis`,
  `funSplitAt`) are already upstream.
- **Keep** the `def` as a project-internal helper: it gives the `w₀`-face a readable name reused across
  the in-file cover chain (`image_boundary_subset_faces` → `frontierCoverFamily` →
  `frontier_subset_frontierCoverFamily`). At 0 external callers and a 1-line body this is a local
  convenience, not an API surface — there is nothing to inline *away* across files, only a do-not-PR
  flag.
- Optional cleanup-lane golf (statement & all 5 call sites unchanged; not a mathlibable action): the
  body could read `⇑expMapBasis ∘ (Equiv.funSplitAt w₀ ℝ).symm ∘ (0, ·)` (or be left as the explicit
  `dite`, which the file's `rw [faceMapZero]`/`change` steps already depend on). Either spelling keeps
  the def project-local.

Next action: keep `faceMapZero` as a project-local `ForMathlib/`-style helper; **do not queue it for a
mathlib PR**. Where its content is conceptually needed it is `expMapBasis ∘ (funSplitAt w₀ ℝ).symm ∘
(0, ·)` — the mathlib chart composed with the standard coordinate-insertion combinator.

---

## Next step

Keep `faceMapZero` project-local (a fine in-file helper naming the `w₀`-face); do not PR to mathlib.
It is a one-liner `def` with 0 external callers and no defeq/diamond/API exemption, and it is a
≤3-call composition of mathlib primitives — the chart `expMapBasis`
(`…/CanonicalEmbedding/NormLeOne.lean:465`) post-composed with the coordinate-insertion combinator
`Equiv.funSplitAt`/`piSplitAt` (`…/Logic/Equiv/Prod.lean:490/480`):
`faceMapZero K = ⇑expMapBasis ∘ (funSplitAt w₀ ℝ).symm ∘ (Prod.mk 0)`. The named literature object is
one level up (the *cover's* Lipschitz-parametrizability — Widmer / GRS §3.3), realised by this file's
*theorems*, not by this `def`.
