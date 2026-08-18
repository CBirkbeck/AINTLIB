# /mathlibable report — `Chebotarev.frontierCoverFamily`

> Step-9 (overview) mathlibable assessment of a single `ForMathlib/` helper **definition**.
> Local Lean build is stale per the task brief, so phases are reasoned from the source statement;
> `lean_loogle`/`lean_leansearch`/Lean-Finder (mathlib-index MCP tools) are not resolvable for
> *project* decls in this env and are substituted by direct `.lake/packages/mathlib` source grep
> (authoritative for "does mathlib have this object"). ChatGPT math MCP is down (Codex `exec`
> error) — recorded `n/a` with reason; WebSearch (3 distinct generality levels) + the source paper
> (Gun–Ramaré–Sivaraman §3.3) + nLab/Stacks carry the literature channel.
>
> This decl is the **assembly** of the per-face maps assessed in the sibling reports
> `faceMapZero.md`, `faceMapSide.md`, `cubeRelabel.md`, `clampUnit_*.md`,
> `exists_lipschitzWith_comp_clampUnit.md` — read together they form one coherent verdict on the
> whole frontier-cover construction.

### Baseline (Phase 0)
- lake build:               not re-run (stale per task brief); reasoning from source statement.
- decl `Chebotarev.frontierCoverFamily`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:284`
- kind:                      **def** (inside `@[expose] public section`; `noncomputable section`).
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the
  Gun–Ramaré–Sivaraman §3.3 (after Debaene) boundary-cell input for the effective lattice-point
  count `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, feeding Widmer / Lang (GTM 110,
  Ch. V §2).
- qualified name:            namespace `Chebotarev` (line 79; **no inner namespace**; `end
  Chebotarev` at line 673), base `frontierCoverFamily`. The prompt's parsed guess
  `Chebotarev.frontierCoverFamily` is **CORRECT** (VERIFIED from source).

---

### Statement (Phase 1)

`frontierCoverFamily` is a **definition** (not a theorem). For a number field `K`, it is the
finite indexed family of cube-parametrizing maps

```
frontierCoverFamily K :
  (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
    (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K
frontierCoverFamily K = Sum.elim (fun _ _ ↦ 0)
  (Sum.elim (fun _ ↦ faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K)
    fun p ↦ faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K)
```

Mathematically: it packages, **into a single function indexed by a finite tag type**, the finitely
many parametrizations of the pieces of the box boundary `∂ paramSet K` (plus the escaping point
`{0}`) whose images cover the frontier of `normAtAllPlaces '' (normLeOne K)` in `realSpace K`. The
index `Unit ⊕ Unit ⊕ ({w ≠ w₀} × Bool)` enumerates:
- `inl ()` — the **zero map** `fun _ ↦ 0` (the closure point that escapes to norm `0` as the
  `w₀`-coordinate `→ −∞`);
- `inr (inl ())` — the **`w₀`-face map** `faceMapZero K`, post-composed with the cube clamp
  `clampUnit` and the relabelling `cubeRelabel` (which turns the `Fin (r−1)` cube into the
  `{w ≠ w₀}`-indexed cube);
- `inr (inr (i, b))` — the **side-face maps** `faceMapSide K i a` for each non-distinguished place
  `i ≠ w₀` and each face value `a = if b then 1 else 0` (`b : Bool`), likewise clamp-and-relabel
  composed.

Each member is a map `[0,1]^{r−1} → realSpace K` (`r = #InfinitePlace K`); the *whole point* of the
def is that the two adjacent theorems can then **quantify over the single index `s`**:
`exists_lipschitzWith_frontierCoverFamily` (`∃ M, ∀ s, LipschitzWith M (frontierCoverFamily K s)`)
and `frontier_subset_frontierCoverFamily`
(`frontier … ⊆ ⋃ s, frontierCoverFamily K s '' Icc 0 1`).

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K] [NumberField K]` — a number field (so `realSpace K`, `w₀`, `expMapBasis`,
  `paramSet K`, `equivFinRank` are all available from mathlib
  `NumberField.CanonicalEmbedding.NormLeOne` + `…/Units/Regulator`).

Hypotheses (Lean side): none (besides the `NumberField K` instance; the file is under
`@[expose] public section` and uses ambient `Classical` only inside the proofs, not the def).

Conclusion (math): n/a — it is a **definition** (an explicit finite family of parametrizing maps,
i.e. the *witness* `(φᵢ)` for the boundary's Lipschitz class), not a proposition.

Conclusion (Lean): n/a — `def`; its *type* is the indexed-family type displayed above.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `ForMathlib/` helper `def` listed under the module's `## Main definitions` only as
internal cover-construction scaffolding ("the finite family covering the `realSpace` frontier",
alongside `faceMapZero`/`faceMapSide`/`clampUnit`/`cubeRelabel`); not a `## Main results`, not named
after a person/place, introduces **no new named mathematical structure** (it is a concrete
`Sum.elim` bundling of three already-defined project maps, not a new topology / category /
measurability notion). Lit width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: **~3 substantive lines** — the nested `Sum.elim (fun _ _ ↦ 0) (Sum.elim (…
faceMapZero …) (fun p ↦ … faceMapSide …))`. Borderline by length, but the body is a single
`Sum.elim` *expression* (a case-split assembling pre-existing maps), so it is treated as essentially
a one-liner-style bundling. **MULTI-LINE / borderline** — kind is `def`, so the exemption table is
still informative:

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | The def is not a sealed barrier; the two consumer theorems `rcases s` on the index and reduce each branch by `change`/direct `exact` (lines 302–306, 323–341), i.e. they **rely on the `Sum.elim` reducing** per tag. It is a transparent case-bundle, not a defeq wall. |
| Avoid typeclass diamonds          | no       | No instance is attached to or routed through `frontierCoverFamily`; it returns a plain function into `realSpace K`. No `Mul`/`Zero`/`AddCommMonoid` search path depends on its name. |
| Mark semantic intent / API name   | no (locally only) | The name marks intent ("the finite family covering the frontier") and is referenced by its two sibling theorems — but **only inside the one declaring file**; **0 external callers** (no other project file imports it — see Phase 6.0). No cross-development API surface a stable mathlib name would protect. |

Conclusion: **MULTI-LINE but with NO exemption that would argue for upstreaming**; it is an
internal indexing/bundling device. Carried into Phase 7: biased toward NO-composable-from-mathlib,
reinforced by Phase 6.0's 0 external callers.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "finite family Lipschitz maps unit cube covering boundary fundamental domain number field counting ideals" | yes  | "$`S`$ is of **Lipschitz class $`(N,L)`$**" iff its boundary is covered by the images of $`N`$ maps $`\varphi_i : [0,1]^{k-1} \to \mathbb{R}^k`$ with $`\mathrm{Lip}(\varphi_i) \le L`$ | arXiv:2411.13522, 1611.10103, 2507.10387 — the **cover/property**, never a named explicit family `(φᵢ)` |
|  2 | WebSearch (general / named method) | "Lipschitz parametrizable boundary Widmer Masser Vaaler finitely many maps unit cube lattice point counting" | yes  | Masser–Vaaler / **Widmer** *Lipschitz class, narrow class, and counting lattice points*: boundary covered by ≤ `W` maps from the cube, error term in `W`, `L`, `λ₁` | RHUL PDF; AMS Proc. 140(2) 2012; msp ANT 11(6). The **named concept = boundary's Lipschitz-parametrizability**, an existential |
|  3 | WebSearch (source paper §3.3)    | "Lipschitz class boundary … Debaene Gun Ramaré Sivaraman counting ideals ray classes section 3.3"      | yes  | **§3.3 is literally titled "Computing the Lipschitz class of the boundary"** of the fundamental domain `F` | arXiv:2208.06602 / JNT 243 (2023) 13–37 (ramare-olivier.github.io PDF) — confirms the *exact* cited reference; the section computes the **class**, the family is its internal witness |
|  4 | ChatGPT MCP                      | 3-part: standard named object for the witness family? / level of abstraction? / is it a `Sum.elim` index bundle of face maps? | n/a  | —                                | **MCP down** (Codex `exec` error this session, as the task brief warned); compensated by channels 1–3, 6, 10 |
|  5 | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/`                                                | n/a  | (directory absent)               | the project has no `.mathlib-quality/references/` dir; no `refs/Chebotarev/` either — recorded `n/a` |
|  6 | nLab                             | "Lipschitz class / lattice point counting / boundary parametrization" (no page for a witness "cover family") | no   | —                                | nLab has no entry for a box-boundary parametrization family; not a categorical object |
|  7 | nCatLab (categorical)            | "cover family"                                                                                          | n/a  | (the only `CoverFamily` in this area is the **categorical-sites** `qcCoverFamily` / `PreZeroHypercoverFamily`) | unrelated: Grothendieck-topology covering families, not a geometry-of-numbers boundary cover — confirms the name collision is spurious |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept (geometry-of-numbers analysis, no scheme/site) |
|  9 | MathOverflow / Math.SE           | (folded into #1–#2) Lipschitz parametrizability of fundamental-domain boundaries                        | yes  | folklore: cover each face of the box by a cube→ℝⁿ map; the *collection* is the witness for the class | corroborated across the Widmer / Barroero–Widmer / Debaene lineage |
| 10 | recent arXiv (last 5 years)      | "counting ideals ray classes Lipschitz boundary cube parametrization frontier number field"            | yes  | GRS §3.3 / Debaene / Widmer Lipschitz-boundary counting | arXiv:2208.06602, 2411.13522, 1611.10103, 2507.10387 — all establish the *class/property*; **none names the explicit witness family** |

Protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific
cover-of-faces / named Lipschitz-class method / the exact source paper §3.3); ChatGPT MCP recorded
`n/a` with reason (down); local refs `n/a` (absent, verified); nLab checked (no entry); nCatLab
checked (only the unrelated categorical-sites `CoverFamily`); Stacks `n/a` with reason; MathOverflow
folded in; arXiv checked (hit — establishes the class, not the witness family).

### Literature summary (Phase 3)

Concept identified as: the **Lipschitz class of the boundary** — Masser–Vaaler / Widmer's notion
that a bounded set `S ⊆ ℝᵏ` is of *Lipschitz class `(N, L)`* iff its boundary is covered by the
images of `N` maps `φᵢ : [0,1]^{k−1} → ℝᵏ` with `Lip(φᵢ) ≤ L`; this is exactly what
Gun–Ramaré–Sivaraman §3.3 ("Computing the Lipschitz class of the boundary") establishes for the
fundamental domain, and it is the regularity input to the lattice-point error term (Widmer; Lang
GTM 110 Ch. V §2). **In every source the named object is the property / the existential statement
`∃ N L (φᵢ), …` — the *collection* of cube maps is the witness, written inline and never abstracted,
named, or given as a standalone indexed family.** `frontierCoverFamily` is precisely *that witness*,
made into a Lean `def` (a `Sum.elim`-indexed function) so that the two theorems can quantify over a
single index `s` instead of handling each face separately.
Sources agree on the standard form: **yes** — the named concept is the *class/cover property*, not a
named witness family.
Most general standard form (of the named concept): "a bounded set whose boundary is the union of
finitely many `L`-Lipschitz images of `[0,1]^{n−1}`" — realised in this file by the **theorems**
`frontier_subset_frontierCoverFamily` + `exists_lipschitzWith_frontierCoverFamily`
(and packaged for export as `normLeOne_frontier_lipschitz_cover`), **not** by this `def`.
Generality dimensions where the literature varies: the ambient (number-field fundamental cone vs.
general bounded set in ℝⁿ vs. heights setting) and the explicitness of `(N, L)`. None of this
attaches to a single "`frontierCoverFamily`" — that granularity (an explicitly enumerated witness
family for *this* box under *this* chart) does not exist in the literature.
Disagreement with the literature: none — the literature simply has no object at this granularity;
`frontierCoverFamily` is a **formalisation-internal indexing device** that bundles the per-face
parametrizations (`faceMapZero`, `faceMapSide`, the zero map) so they can be quantified uniformly.

---

### Generality analysis — `Chebotarev.frontierCoverFamily`

Literature-standard form (from Phase 3): there is **no general literature statement to match** at
the level of the witness *family* — the named object is the *Lipschitz class* (a property), one
level up, and it is realised by this file's theorems. As a *family*, `frontierCoverFamily` is
maximally **specific** (the explicit faces of *one* box `paramSet K` under *one* chart `expMapBasis`
of *this* number field `K`); it is not a specialisation of some general definition that mathlib
would want in general form.

| # | Parameter / hypothesis        | Current Lean form                                   | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-----------------------------------------------------|----------------------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K]`             | number field (fixes `realSpace`, `w₀`, `expMapBasis`, the box `paramSet K`) | none — the family is *about* this number-field box | NO | the chart, the distinguished place `w₀`, and the box geometry are number-field data; nothing to weaken |
| 2 | index `Unit ⊕ Unit ⊕ ({w ≠ w₀} × Bool)` | the explicit tag enumerating {zero map, `w₀`-face, side faces × {0,1}} | n/a — the literature leaves the witness collection inline | NO | the index *is* the enumeration of the box's faces; it is not an arbitrary parameter to abstract |
| 3 | branch maps `faceMapZero` / `faceMapSide` / `0` | the three bespoke per-face parametrizations (each itself project-local, see sibling reports) | n/a | NO | each branch is the specific face's parametrization; abstracting them deletes the family's reason to exist |
| 4 | post-composition `∘ clampUnit _ ∘ cubeRelabel K` | clamp to the unit cube, relabel `Fin (r−1) ≃ {w ≠ w₀}` | n/a | NO | both factors are fixed plumbing (`clampUnit`, `cubeRelabel`) tied to this construction |

### Generality verdict (Phase 4b)

The current form is: **NEITHER maximally general NOR meaningfully generalisable** — it is a
maximally *specific* witness family (the explicit faces of one number-field box under one chart).
There is no literature-standard *family* form to aim at; the closest *named* statement (the
boundary's Lipschitz class / parametrizability) is one level up and is realised by the **theorems**
in this file (`frontier_subset_frontierCoverFamily`, `exists_lipschitzWith_frontierCoverFamily`,
exported as `normLeOne_frontier_lipschitz_cover`), not by this `def`.
Number of weakening opportunities found: **0** that would yield a mathlib-shaped general definition.
Proposed restatement: **none** — this decl is not a restate-and-upstream candidate.
Cost of restatement: **n/a**.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | bundled-hypothesis preamble → typeclass/instance?                                 | no       | the only hypothesis is the mathlib typeclass `NumberField K` | — |
|  2 | sequences/metric → filters/topological?                                           | no       | nothing limit-shaped; it is a finite indexed family of maps | — |
|  3 | construct object → universal-property class?                                      | no       | an explicit witness family has no universal property to characterise; the *property* it witnesses (Lipschitz class) is the theorem, not this def | — |
|  4 | set-with-predicate → bundled substructure?                                        | no       | no substructure; it is a function `index → cube → realSpace` | — |
|  5 | field/metric-specific → weaken typeclass hierarchy?                               | no       | the `ℝ` / number-field / `expMapBasis` / box data is the *subject*, not an over-strong hypothesis | — |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a | — |
|  7 | concrete index → arbitrary additive/ordered structure?                            | no       | the index enumerates *this* box's faces; it is fixed by the geometry, not a `ℕ`/`ℤ` to abstract | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The only "improvement" imaginable is to drop the explicit `Sum.elim`
family entirely and have the cover theorem `∃ N (φ : Fin N → …), …` produce the witness inline
(which is in fact already done one layer out: `normLeOne_frontier_lipschitz_cover` re-packages
`frontierCoverFamily` through `Fintype.equivFin` into a `Fin m`-indexed existential, lines 348–358).
That is a *refactor of single-use scaffolding*, not a modernisation that improves the library's
organisation or unlocks downstream mathlib API. No real mathematical-organisation improvement
exists, because the object itself is a formalisation-internal indexing device.

---

### Diamond / defeq risk — `Chebotarev.frontierCoverFamily` (Phase 4.5 — kind is `def`)

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond             | none    | carries no instance and is not in any instance-search path; returns a bare function `index → (Fin (r−1) → ℝ) → realSpace K`. No `Mul`/`Zero`/`AddCommMonoid` target collides. |
| 2 | Reducibility leak             | low     | not `@[reducible]`; semi-reducible. The two consumer theorems `rcases` the index and reduce each `Sum.elim` branch (lines 302–306, 323–341) — so its case structure is deliberately exposed locally. Harmless at the project's scale; would be a non-issue in mathlib too (it is a plain `Sum.elim` of functions). |
| 3 | Non-canonical unfolding       | low     | `rcases s with _ \| _ \| p` + per-branch `exact`/`change` succeed because each `Sum.elim` arm is a direct composition; no surprising `simp`/`rfl` behaviour. |
| 4 | Instance priority collision   | n/a     | not an `instance`. |
| 5 | Universe-polymorphism issues  | none    | everything is at `Type 0` (`realSpace K`, `ℝ`, places, the finite index); no universe annotation forced. |
| 6 | Coercion ambiguity            | none    | no `CoeFun`/`CoeSort`; the branch maps coerce through their existing function types, unchanged here. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (rows 2–3 low, the rest none/n/a). Top risks: none HIGH. No mitigation needed.
This does not gate a NO verdict; recorded for completeness.

---

### Mathlib search-status: `Chebotarev.frontierCoverFamily`

[A] Lean-Finder       n/a (deferred/MCP tool not resolvable for *project* decls in this env)
[B] Loogle            n/a (`lean_loogle` not resolvable for project decls; substituted by direct mathlib-src grep [D])
[C] LeanSearch        n/a (`lean_leansearch` not resolvable for project decls; substituted by WebSearch + mathlib-src grep)
[D] Grep mathlib src  `frontierCover|coverFamily|boundaryCover|faceMap` over `.lake/packages/mathlib/Mathlib/`
                      → `frontierCover`/`boundaryCover`/`faceMap`: **0 hits**; `coverFamily`: only the
                      **categorical-sites** `qcCoverFamily` (`AlgebraicGeometry/Sites/QuasiCompact.lean:39`)
                      and `PreZeroHypercoverFamily` (`CategoryTheory/Sites/Hypercover/ZeroFamily.lean`) —
                      **unrelated** (Grothendieck-topology covering families). Also grepped for any
                      *Lipschitz-class / Lipschitz-parametrizability* notion
                      (`LipschitzClass|LipschitzParametriz|coverByLipschitz|frontier.*⊆.*⋃.*Icc`) → **0 hits**;
                      and `boundary.*Lipschitz|Lipschitz.*frontier` in `MeasureTheory/`+`NumberTheory/` →
                      no boundary-cover theorem.
[E] Name pattern      grep `frontierCoverFamily` / `*CoverFamily*` / `*faceMap*` over the mathlib tree →
                      none in geometry-of-numbers / number theory.

Searched for both:
  - the user's current form (a `def` named `frontierCoverFamily`, the explicit witness family) —
    **not in mathlib, and structurally cannot be**: grep of the whole mathlib tree → 0 relevant hits;
    the object is project-local glue;
  - the named literature concept it witnesses + its building blocks (re-aim targets):
      · **the *Lipschitz class / Lipschitz-parametrizability* of a boundary** → **NOT in mathlib at
        all** (0 hits for any such notion; mathlib has no "boundary covered by finitely many
        Lipschitz cube-images" predicate or theorem). So there is no `D'` to re-aim at, and the
        *property* itself (the genuinely interesting object) is what this file's **theorems** supply;
      · the branch maps — `faceMapZero`, `faceMapSide`, `cubeRelabel`, `clampUnit` — are themselves
        **project-local** (sibling reports: `faceMapZero` NO-composable; `cubeRelabel` =
        `Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank`, NO-mathlib-has-it; `clampUnit` =
        `Set.projIcc`-pi); mathlib supplies *their* pieces (`expMapBasis`
        `…/CanonicalEmbedding/NormLeOne.lean:465`, `Equiv.funSplitAt`/`piCongrLeft'`, `Set.projIcc`)
        but not the faces;
      · the bundling combinator `Sum.elim` → **FOUND** in core/`Mathlib` (`Sum.elim`), the standard
        case-analysis function on a sum type — this is the only "general" ingredient and it is fully
        upstream.

Concluded: **"not in mathlib (all methods exhausted, plus the literature-standard *property* form)
— and structurally cannot be: `frontierCoverFamily` is a `Sum.elim` bundle of project-local face
maps."** Mathlib has the bundling primitive (`Sum.elim`) and the deepest building block
(`expMapBasis`), but neither the witness family nor even the Lipschitz-class *property* it serves.

---

### Call sites — `Chebotarev.frontierCoverFamily`

Internal use count: **K = 0 external** — `grep -rn "frontierCoverFamily" projects/` returns **only**
the declaring file `ForMathlib/NormLeOneLipschitz.lean` (the downstream consumers
`IdealCongruenceCount.lean` / `ZetaProduct.lean` reference the **exported theorem**
`normLeOne_frontier_lipschitz_cover[_index]`, *never* the `frontierCoverFamily` def). Within the
declaring file the substantive (non-docstring) uses are:

| Caller file:line                  | Usage pattern (one-line excerpt)                                                  |
|-----------------------------------|------------------------------------------------------------------------------------|
| NormLeOneLipschitz.lean:296       | `∃ M, ∀ s, LipschitzWith M (frontierCoverFamily K s)` (its own Lipschitz theorem `exists_lipschitzWith_frontierCoverFamily`) |
| NormLeOneLipschitz.lean:316       | `frontier … ⊆ ⋃ s, frontierCoverFamily K s '' Icc 0 1` (its own cover theorem `frontier_subset_frontierCoverFamily`) |
| NormLeOneLipschitz.lean:323/335/341 | `⟨Sum.inr (Sum.inl ()), …⟩` / `⟨Sum.inr (Sum.inr (i,b)), …⟩` / `⟨Sum.inl (), …⟩` (membership witnesses, by index tag, inside the cover proof) |
| NormLeOneLipschitz.lean:356/357   | `fun j ↦ frontierCoverFamily K (e.symm j)` (re-indexed through `Fintype.equivFin` to a `Fin m`-family for the exported `normLeOne_frontier_lipschitz_cover`) |

Inline-derivation grep (was an equivalent family re-derived elsewhere without using
`frontierCoverFamily`?):
  - (none) — the family is referenced through this def at every site; it is the single in-file
    bundling of the faces, immediately consumed by its own two theorems and then dissolved into a
    `Fin m`-existential by `normLeOne_frontier_lipschitz_cover`.

Composability signal: **K = 0 external callers; all uses confined to one file**, and even there only
as the **index argument to its own two theorems** (which are themselves repackaged into an
existential the moment they leave the file). This is the strongest possible *single-file
indexing-device* signal — the def exists purely so `∀ s` / `⋃ s` can range over the faces in one
breath. Combined with Phase 2b (no upstreaming exemption) and Phase 6 (a trivial `Sum.elim` of
project-local maps), the case for NO is decisive.

---

### Composition check (Phase 6)

Can `frontierCoverFamily` be expressed as a ≤3-call composition / assembly of existing mathlib decls
(so it could be inlined rather than upstreamed)?

Attempt 1 — it is **definitionally** a `Sum.elim` of three maps, and the maps are themselves
≤3-call compositions over mathlib (per the sibling reports):
```lean
-- frontierCoverFamily K  =
--   Sum.elim (fun _ _ ↦ 0)
--     (Sum.elim (fun _ ↦ faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K)
--       (fun p ↦ faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K))
-- where, from the sibling assessments, each ingredient is mathlib-composable / mathlib-existing:
--   • cubeRelabel K            = ⇑(Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank)   [cubeRelabel.md: NO-mathlib-has-it]
--   • clampUnit _              = fun c i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ) [clampUnit_*: Set.projIcc-pi]
--   • faceMapZero K            = ⇑expMapBasis ∘ (Equiv.funSplitAt w₀ ℝ).symm ∘ (Prod.mk 0)  [faceMapZero.md: NO-composable]
--   • faceMapSide K i a        = (· i) • (expMapBasis ∘ insert-two-coords)                  [faceMapSide.md: project-local]
```
  - Mathlib decls used: `Sum.elim` (sum-type case analysis, upstream); plus, transitively,
    `expMapBasis` (`…/NormLeOne.lean:465`), `Equiv.piCongrLeft'`/`funSplitAt`
    (`…/Logic/Equiv/Basic.lean:803`, `…/Logic/Equiv/Prod.lean:490`), `Set.projIcc`.
  - Result: **succeeds as a definitional identity** — `frontierCoverFamily` *is* `Sum.elim`
    applied to three branch maps, each of which is a ≤3-call mathlib composition (or, for
    `cubeRelabel`, an outright mathlib decl). The assembly adds no new mathematical content: it is
    the case-bundling of pre-existing pieces, indexed by the box's faces.
  - Notes: the **only** thing `frontierCoverFamily` contributes beyond `Sum.elim` + the branch maps
    is the *choice of index type* and *which face goes in which slot* — i.e. the enumeration of the
    boundary faces. That enumeration is precisely the inline-witness step the literature never names.

Conclusion: **COMPOSABLE** (in the "assembled from mathlib + project-local pieces via `Sum.elim`"
sense). `frontierCoverFamily = Sum.elim (zero) (Sum.elim (faceMapZero∘clamp∘relabel)
(faceMapSide…∘clamp∘relabel))`, where every branch is a ≤3-call composition of mathlib primitives
(or a mathlib decl). No new mathlib lemma/def is justified; the family is an internal indexing
device, immediately repackaged into a `Fin m`-existential by `normLeOne_frontier_lipschitz_cover`.

---

## Verdict: `Chebotarev.frontierCoverFamily`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the **named** object is the *Lipschitz class of the boundary*
  (Masser–Vaaler / Widmer; **Gun–Ramaré–Sivaraman §3.3 — literally titled "Computing the Lipschitz
  class of the boundary"**, the file's cited reference) — a *property* `∃ N L (φᵢ), …`. The explicit
  witness family `(φᵢ)` is **inline scaffolding** in every source, never a named standalone object
  (3 WebSearch levels + the source paper + nLab/Stacks concur; ChatGPT MCP down → `n/a`).
- Generality analysis (Phase 4): maximally **specific** (the explicit faces of one number-field box
  under one chart), 0 weakenings to a mathlib-shaped general def; Phase 4c found only a *refactor*
  of single-use scaffolding (already done one layer out by `normLeOne_frontier_lipschitz_cover`),
  not a modernisation. Phase 4.5 risk: **LOW** (no diamond/coercion issues).
- Mathlib search (Phase 5): **not in mathlib** — `frontierCoverFamily` absent (the only
  `*CoverFamily` is the unrelated categorical-sites `qcCoverFamily`/`PreZeroHypercoverFamily`); and
  the *Lipschitz-class property* it witnesses is **also absent** from mathlib (0 hits for any such
  notion). Building blocks present: `Sum.elim` (the bundling), `expMapBasis`
  (`…/NormLeOne.lean:465`), `Equiv.piCongrLeft'`/`funSplitAt`, `Set.projIcc` — but not the faces and
  not the family.
- Composition check (Phase 6): **COMPOSABLE** — `frontierCoverFamily = Sum.elim (fun _ _ ↦ 0)
  (Sum.elim (faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K) (fun p ↦ faceMapSide K p.1 … ∘ clampUnit _
  ∘ cubeRelabel K))`, a `Sum.elim` bundle whose branches are each ≤3-call mathlib compositions.

**Rationale:**

`frontierCoverFamily` is the explicit, `Sum.elim`-indexed **witness family** `(φᵢ)` for the
boundary's *Lipschitz class* — the property that the frontier of `normAtAllPlaces '' (normLeOne K)`
is covered by finitely many `M`-Lipschitz images of the unit cube `[0,1]^{r−1}`. The geometry-of-
numbers literature this construction implements (Masser–Vaaler; Widmer's *Lipschitz class, narrow
class, and counting lattice points*; and the file's cited Gun–Ramaré–Sivaraman §3.3, whose title is
*exactly* "Computing the Lipschitz class of the boundary") names the **property** — the existential
"`∃ N, L, (φᵢ), …`" — but **never** the explicit family of cube maps that witnesses it; that family
is always written inline inside the estimate. So there is no literature-standard *family* object to
upstream, and the genuinely-named object (the Lipschitz-class *property*) is what this file's
**theorems** supply — `frontier_subset_frontierCoverFamily` +
`exists_lipschitzWith_frontierCoverFamily`, exported as `normLeOne_frontier_lipschitz_cover`. Mathlib
has neither the family nor even the property (Phase 5: 0 hits for any Lipschitz-parametrizability
notion; the only `*CoverFamily` decls are unrelated Grothendieck-topology covering families).

Structurally, `frontierCoverFamily` *is* a `Sum.elim` bundling of three already-defined project maps
(the zero map, `faceMapZero`, `faceMapSide`), each post-composed with `clampUnit` and `cubeRelabel`,
and each of those is itself a ≤3-call composition of mathlib primitives (or, for `cubeRelabel`, the
outright mathlib decl `Equiv.piCongrLeft'` — see the sibling reports). The def's *only* contribution
beyond `Sum.elim` + its branch maps is the **enumeration of the box's faces into a single index
type** — exactly the inline-witness bookkeeping the literature never abstracts. That is the
textbook NO-composable-from-mathlib profile, reinforced from three independent directions: Phase 2b
(no upstreaming exemption — it guards no defeq barrier and no instance diamond, and its only API
consumers are in-file), Phase 6.0 (**0 external callers**: downstream code uses the *theorem*
`normLeOne_frontier_lipschitz_cover`, never this def), and the fact that the family is dissolved
back into a `Fin m`-existential the instant it leaves the file (lines 356–358). This matches the
sibling verdicts on every piece of the same machinery (`faceMapZero` NO-composable; `cubeRelabel`
NO-mathlib-has-it; `clampUnit` a `Set.projIcc`-pi wrapper) — the whole frontier-cover construction
is project-local scaffolding, and `frontierCoverFamily` is its index/assembly layer.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; `frontierCoverFamily` is a `Sum.elim` assembly over them whose
subject (the explicit faces of one number-field box under one chart) is not a mathlib-shaped object
— so it should not be queued for a mathlib PR. This is a **keep-local / do-not-PR** recommendation,
**not** a delete-from-the-library one: `main` keeps the producer's helper as written — enumerating
the boundary faces into one index so `∀ s` / `⋃ s` range over them is the right *local* abstraction
(it is what makes `exists_lipschitzWith_frontierCoverFamily` and
`frontier_subset_frontierCoverFamily` one-liner-per-branch); the point is only that it is not
upstreamable.

Mathlib building blocks (qualified names + paths):
- `Sum.elim` — core/`Mathlib` (sum-type case analysis; the bundling combinator the def *is*).
- `expMapBasis` — `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:465`
  (the log-exp chart the face maps push through), with `expMapBasis_apply''` (`:504`) the
  `exp(x w₀) • …` decomposition `faceMapSide` exploits.
- `Equiv.piCongrLeft'` — `Mathlib/Logic/Equiv/Basic.lean:803` (`cubeRelabel` *is* this, applied to
  `equivFinRank`; metrically `IsometryEquiv.piCongrLeft'`, `…/Isometry.lean:576`).
- `Equiv.funSplitAt` / `Equiv.piSplitAt` — `Mathlib/Logic/Equiv/Prod.lean:490`/`:480`
  (the "insert one coordinate" map inside `faceMapZero`/`faceMapSide`).
- `Set.projIcc` — `Mathlib/Order/Interval/Set/ProjIcc.lean` (`clampUnit` is this applied coordinatewise).

Composition sketch (the def, unfolded to its assembly):
```lean
-- frontierCoverFamily K  =
--   Sum.elim (fun _ _ ↦ 0)
--     (Sum.elim (fun _ ↦ faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K)
--       (fun p ↦ faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K))
-- each branch ≤3-call-composable over mathlib (cubeRelabel = Equiv.piCongrLeft' (fun _ ↦ ℝ) equivFinRank;
-- clampUnit = Set.projIcc-pi; faceMapZero = expMapBasis ∘ (funSplitAt w₀ ℝ).symm ∘ (0,·); faceMapSide analogous).
```

Call sites in the project (from Phase 6.0): **K = 0 external**; in-file only (lines 296, 316,
323/335/341, 356–357) — and even there only as the index argument to its own two theorems, which
`normLeOne_frontier_lipschitz_cover` immediately repackages into a `Fin m`-existential.

Refactor plan:
- Do **not** open a mathlib PR for `frontierCoverFamily` (nor for its two sibling theorems
  `exists_lipschitzWith_frontierCoverFamily` / `frontier_subset_frontierCoverFamily`, which are the
  in-file proof of the Lipschitz-class property; the *exported* statement
  `normLeOne_frontier_lipschitz_cover` is the natural public surface, and even that is bespoke to
  this number-field region). The reusable pieces (`Sum.elim`, `expMapBasis`, `Equiv.piCongrLeft'`,
  `funSplitAt`, `Set.projIcc`) are already upstream.
- **Keep** the `def` as a project-internal helper: it bundles the boundary faces into one index so
  the cover can be quantified uniformly; at 0 external callers this is local plumbing, not an API
  surface — there is nothing to inline *away* across files, only a do-not-PR flag.
- (If one ever *did* want to upstream something from this file, the mathlib-shaped target is **not**
  this family but a general **"Lipschitz class / Lipschitz-parametrizability of a boundary"
  predicate + the lattice-count error theorem keyed on it** — Widmer's framework, currently entirely
  absent from mathlib. That is a much larger, separate `/develop`-scale contribution; this `def`
  would be an internal witness inside *that* development too, not the contribution itself.)

Next action: keep `frontierCoverFamily` project-local (a fine in-file index/assembly of the boundary
faces); **do not queue it for a mathlib PR**. It is a `Sum.elim` bundle of project-local maps, each
a ≤3-call composition of mathlib primitives, with 0 external callers; the named literature object it
serves (the boundary's *Lipschitz class*) is supplied by this file's theorems, and even that
property is absent from mathlib (a separate, larger upstreaming target if ever desired).

---

## Next step

Keep `frontierCoverFamily` project-local; do not PR to mathlib. It is a `def` that merely bundles
the box's boundary faces — the zero map, `faceMapZero`, and the `faceMapSide i a` — into one
`Sum.elim`-indexed family so the two cover theorems can quantify over a single index `s`; every
branch is a ≤3-call composition of mathlib primitives (`expMapBasis`, `Equiv.piCongrLeft'`/
`funSplitAt`, `Set.projIcc`) glued by the upstream `Sum.elim`, and it has 0 external callers
(downstream code consumes the exported theorem `normLeOne_frontier_lipschitz_cover`, never this
def). The named literature object (the *Lipschitz class of the boundary*, Masser–Vaaler / Widmer /
GRS §3.3) is the existential *property* — realised here by `frontier_subset_frontierCoverFamily` +
`exists_lipschitzWith_frontierCoverFamily` — not this witness family; and mathlib has no such
Lipschitz-parametrizability notion at all (that would be a separate, much larger contribution).
