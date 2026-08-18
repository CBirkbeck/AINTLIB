# /mathlibable report — `Chebotarev.mem_iUnion_image_liftToMixed_of_eq`

## Baseline (Phase 0)
- lake build:               not run (local build is stale per task brief; reasoning from source — permitted)
- decl `Chebotarev.mem_iUnion_image_liftToMixed_of_eq`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:558`
- kind:                      theorem
- has sorry:                 no
- namespace:                 `Chebotarev` (file `namespace Chebotarev` at line 79, `end Chebotarev` at 673)
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` in `mixedSpace K`
  — the quantitative boundary-regularity input (Gun–Ramaré–Sivaraman / Debaene, after Widmer/Lang)
  for the effective lattice-point count `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.

## Statement (Phase 1)

`mem_iUnion_image_liftToMixed_of_eq` is a **fibre-covering / lift-surjectivity** theorem:

> Let `ψ : [0,1]^{r-1} → realSpace K` be a cube-parametrization map (`r = #InfinitePlace K`),
> `c' ∈ [0,1]^{r-1}`, and `x ∈ mixedSpace K` a point whose coordinatewise modulus image equals
> `ψ c'`, i.e. `normAtAllPlaces x = ψ c'`. Then `x` lies in the union, over all sign patterns
> `ε : {real places} → Bool`, of the cube image `liftToMixed K ψ ε '' Icc 0 1` of the lift map.

In words: any mixed-space point whose place-wise moduli are given by a cube point `ψ c'` is
**reconstructed** from those moduli by choosing (i) a `±1` sign at each *real* place and (ii) a
*phase* `exp((2πθ − π)i)` at each *complex* place, with the phase angles `θ` and the original `c'`
packed together into the `d − 1` cube coordinates (`d = [K:ℚ]`, via `mixedCubeEquiv`).

Variables / typeclasses (Lean side):
- `K` a number field (implicit via section variables; `[NumberField K]`, `[Field K]`).
- `ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K` — a cover map (project object).
- `c' : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ` — a cube point.

Hypotheses (Lean side):
- `hc' : c' ∈ Icc (0 : _) 1` — `c'` is in the unit cube.
- `hx : normAtAllPlaces x = ψ c'` — the modulus image of `x` matches the cube point.

Conclusion (Lean):
`x ∈ ⋃ ε : {w : InfinitePlace K // IsReal w} → Bool, liftToMixed K ψ ε '' Icc 0 1`.

Proof idea (≈28 lines): take `ε_w = decide (0 ≤ x.1 w)` at real places; for each complex
coordinate `x.2 w` use the polar decomposition `exists_phase_mem_Icc_mul_exp` (itself
`Complex.norm_mul_exp_arg_mul_I` + bookkeeping) to get a phase `θ_w ∈ [0,1]`; assemble the cube
point `c` from `c'` and `(θ_w)` via `mixedCubeEquiv`; then `liftToMixed K ψ ε c = x` by
`Prod.ext` + the modulus identities `ψ c' w = |x.1 w|` / `‖x.2 w‖` (from unfolding
`normAtAllPlaces`).

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a single-purpose helper lemma in a `ForMathlib/` file; not a named theorem, not a `def`,
not a `## Main results` entry. It is one of three steps building
`frontier_normLeOne_subset_iUnion_image_liftToMixed_aux` (private) and thence the file's actual
main results. (Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (Body is ≈28
substantive lines.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "mixed space number field modulus map fibre signs phases polar coordinates parametrization surjective" | no   | —                   | Returns generic "parametrization" + mixed-polynomial-link papers; nothing about this fibre statement |
| 2  | WebSearch (general form)         | "polar coordinate decomposition complex number modulus argument every complex z equals norm·exp(i·arg)" | yes  | `z = r(cosθ + i sinθ) = r·exp(iθ)`, the polar form | This is the *elementary* underlying fact (per-complex-coordinate); standard since Euler. The number-field fibre wrapper is not a named result. |
| 3  | WebSearch (named-after / context)| "Gun Ramare Sivaraman counting ideals ray classes Debaene Lipschitz parametrization frontier fundamental domain" | yes (context) | GRS, J. Number Theory 243 (2023); Debaene; Widmer | Confirms the *ambient argument* (Lipschitz-parametrizable frontier `D_X` is `(n-1)`-Lipschitz; Widmer/Debaene partition of the fundamental parallelepiped). The fibre-lift lemma is an internal step of such arguments, never isolated as a citable result. |
| 4  | ChatGPT MCP                      | "Is the sign+phase fibre-surjectivity of the mixed-space modulus map a recognised named lemma?"        | n/a  | — (tool down)       | **Codex backend failed both attempts** (`Command failed … Reading additional input from stdin`). Recorded n/a; the standard-form question is answered by channels 2/3/8 and by the mathlib search (Phase 5). |
| 5  | Local references                 | (no `.mathlib-quality/references/` PDFs present for Chebotarev; `refs/` is gitignored & not symlinked)  | n/a  | —                   | Directory absent in this worktree — recorded n/a per protocol. The module docstring itself cites GRS §3.3 + Widmer/Lang GTM 110 Ch. V §2. |
| 6  | nLab                             | "polar coordinates / modulus-argument decomposition"                                                   | n/a  | —                   | nLab has no page for this number-theoretic fibre-cover construction; the polar decomposition it does cover is the elementary one (channel 2). Not a categorical concept. |
| 7  | nCatLab                          | —                                                                                                      | n/a  | —                   | Not a categorical concept — no functorial/universal-property content; pure point-set reconstruction. |
| 8  | Stacks Project                   | —                                                                                                      | n/a  | —                   | Not an algebraic-geometry concept (Archimedean places / `mixedSpace` are analytic NT, outside Stacks' scope). |
| 9  | MathOverflow / Math.SE           | (covered by WebSearch channels 1–3; analytic-NT lattice-point-count boundary lemmas)                   | no   | —                   | No standalone Q/A on "sign+phase fibre of the mixed-space modulus map"; the topic appears only inside full lattice-count write-ups. |
| 10 | recent arXiv (last 5 years)      | "Counting ideals … Lipschitz parametrization frontier number field" (arXiv:2208.06602; 2604.19681)     | yes (context) | Debaene/Widmer Lipschitz-cover machinery | The cover *exists* in these papers; the per-fibre sign+phase lift is implicit bookkeeping, not a displayed lemma. |

### Literature summary (Phase 3)

Concept identified as: **the elementary sign-and-modulus / polar decomposition** of `ℝ^{r₁} × ℂ^{r₂}`
relative to the coordinatewise-modulus map — the fact that the modulus map is surjective onto the
nonnegative orthant with fibres `{±1}^{r₁} × (S¹)^{r₂}` — here *specialised and re-packaged* as
"membership in a finite union of cube-image lifts indexed by sign patterns ε", glued to the
project's bespoke `liftToMixed`/`mixedCubeEquiv` cube encoding.

Sources agree on the standard form: **yes for the underlying fact** (polar form `z = ‖z‖·exp(iθ)`,
sign `x = ±|x|`); **no recognised standalone form for the wrapper** — the number-field fibre-lift
statement is not a named/citable lemma anywhere. It is proof-scaffolding internal to the
GRS/Debaene/Widmer Lipschitz-boundary lattice-count argument.

Most general standard form: the per-coordinate polar/sign decomposition (`ℂ → ℝ≥0 × S¹`, `ℝ → ℝ≥0 × {±1}`),
which mathlib already has both pointwise (`Complex.norm_mul_exp_arg_mul_I`) and bundled for the
mixed space (`mixedEmbedding.polarCoord` / `polarSpaceCoord`, see Phase 5).

Disagreement with the literature: none. The literature has the *elementary* fact at full generality;
it does not have this exact wrapper, because the wrapper exists only to feed `frontierCoverFamily`.

Empty-literature note: the search did NOT return a standalone form for the wrapper. Per the
verdicts reference ("Treating literature absence as YES"), absence here is a **signal the decl is
proof-specific**, not a signal to add it — pushing Phase 7 toward NO-composable / BORDERLINE.

## Generality analysis — `mem_iUnion_image_liftToMixed_of_eq`

Literature-standard form (from Phase 3): per-coordinate polar/sign decomposition of `mixedSpace K`;
in mathlib idiom, the `mixedEmbedding.polarCoord` change-of-variables homeomorphism.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `ψ`, `liftToMixed K ψ ε`, `mixedCubeEquiv`, `Icc 0 1` cube | project-bespoke cube-encoded lift | mathlib's `mixedEmbedding.polarCoord.symm` (the canonical modulus+phase reconstruction) | n/a — different formulation entirely | The statement is *defined in terms of* the project objects; there is no "weaker `ψ`" — the whole statement would have to be restated against `polarCoord` to be mathlib-idiomatic. |
| 2 | `hc' : c' ∈ Icc 0 1` | unit-cube membership | — | NO | Intrinsic to the cube parametrization; not a generality axis. |
| 3 | `K` number field | `[NumberField K]` | same | NO | Already the right generality for anything about `mixedSpace K`. |

### Generality verdict (Phase 4b)

The current form is: **NEITHER maximally general NOR a clean specialisation** — it is *expressed in
project-local vocabulary* (`liftToMixed`, `mixedCubeEquiv`, `frontierCoverFamily`-shaped cube
images) with **no literature-standard counterpart to generalise toward**. Number of
literature-driven weakening opportunities on the *given* statement: 0 (the statement is not "too
special", it is "too bespoke").
Proposed restatement: n/a as a weakening. The only mathlib-idiomatic move would be to *re-found* the
whole construction on `mixedEmbedding.polarCoord` (Phase 4c), which changes the statement, not just
its hypotheses.
Cost of any such restatement: **EXPENSIVE** (re-derive the cover against `polarCoord`; new proof).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1  | "let X be a foo" preamble → typeclass/instance? | no | — | The hypotheses are already data (`ψ`, `c'`, `x`), not a structure-bearing preamble. |
| 2  | sequences/metric → filters/topology? | no | — | No convergence content; this is an exact algebraic reconstruction identity. |
| 3  | construct an object → universal-property class? | **partially** | restate "x is in the union of cube-lift images" via `mixedEmbedding.polarCoord.symm` (mathlib's universal modulus+phase change of vars) instead of the bespoke `liftToMixed`/`mixedCubeEquiv` | reuses mathlib's `polarCoord` API (measurability, integral change-of-vars) — but this is really a comment on the *parent def* `liftToMixed`, not this lemma. |
| 4  | set+closure-predicate → bundled substructure? | no | — | No substructure here. |
| 5  | vector-space/metric/field-specific → weaker typeclass? | no | — | Already over a number field's mixed space; no over-strong field/metric hypothesis. |
| 6  | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7  | concrete index (ℕ/ℤ/ℝ) → general monoid/group? | no | — | The indices (`Fin (… - 1)`, place subtypes) are intrinsic to `K`; not artificially concrete. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it targets the parent `def liftToMixed`, not this lemma in
isolation.** The contemporary mathlib formulation of "reconstruct a mixed-space point from its
moduli by signs + phases" is `mixedEmbedding.polarCoord` (an `OpenPartialHomeomorph` /
measurable change of variables). A mathlib-native version of the whole frontier-cover development
would phrase the cover through `polarCoord.symm` rather than the hand-rolled `liftToMixed` +
`mixedCubeEquiv` cube encoding.
- Cost: **EXPENSIVE** (a re-foundation of the cover construction, not a restatement of one lemma).
- Real mathematical improvement: yes at the *construction* level (compose with mathlib's polar
  change-of-variables API), but this lemma is a leaf of that construction — modernising it alone is
  not meaningful; it rides on whatever `liftToMixed` becomes.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (introduces no definitional equalities or instance-search paths).

## Mathlib search-status: `Chebotarev.mem_iUnion_image_liftToMixed_of_eq`

[A] Lean-Finder       n/a (mathlib index unavailable offline; covered by WebSearch + grep)  — no hits
[B] Loogle            conceptual: `mixedSpace`/`normAtAllPlaces` + `⋃`/`image`/`Icc` surjectivity — no exact-form hit (the statement's head symbols `liftToMixed`/`frontierCoverFamily` are project-local, so no mathlib lemma can match by shape)
[C] LeanSearch        "every mixed space point recovered from its place moduli by signs and phases" — resolves to the polar-coordinate change of variables, not this union statement
[D] Grep mathlib src  `liftToMixed`, `frontierCoverFamily`, `mixedCubeEquiv`, `mem_iUnion_image_liftToMixed` over `.lake/packages/mathlib/Mathlib/` → **0 hits** (all project-local). `normAtAllPlaces` surjectivity/fibre lemmas → only `normAtAllPlaces_image_preimage_*` (norm-stability of preimage), `mixedSpaceOfRealSpace` (the canonical section `realSpace → mixedSpace`), and the `polarCoord` family. `Complex.norm_mul_exp_arg_mul_I` (the polar identity this lemma's `exists_phase_mem_Icc_mul_exp` is built on) → present at `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:56`.
[E] Name pattern      `lean_local_search` unavailable (stale build); grep on the base name confirms the decl exists only in this project.

Searched for both:
  - the user's current form (the `⋃ ε, liftToMixed '' Icc` membership) — **not in mathlib** (head symbols are project-local).
  - the literature-standard form (polar/sign decomposition of the mixed space) — **mathlib HAS the
    building blocks**: `mixedEmbedding.polarCoord` / `polarSpaceCoord` (PolarCoord.lean) for the
    bundled modulus+phase change of variables, `mixedSpaceOfRealSpace` for the nonnegative section,
    and `Complex.norm_mul_exp_arg_mul_I` for the per-coordinate polar form.

Concluded: **the user's exact form is not in mathlib (it is phrased in project-local vocabulary);
the underlying mathematical content — sign+phase reconstruction of the mixed space — is covered by
mathlib's `mixedEmbedding.polarCoord` family + `Complex.norm_mul_exp_arg_mul_I`, but NOT in the
"finite union of cube-image lifts indexed by ε" packaging this lemma needs.**

## Call sites — `Chebotarev.mem_iUnion_image_liftToMixed_of_eq`

Internal use count: **1**  (within the project, excluding the declaring lemma itself)
External-to-file callers: **0** files (the sole use is in the *same* file)
External-to-project callers: **0**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `…/ForMathlib/NormLeOneLipschitz.lean:615` | `Set.mem_iUnion.mp (mem_iUnion_image_liftToMixed_of_eq (ψ := frontierCoverFamily K s) (c' := c') (hc' := hc') (x := x) (hx := hxeq.symm))` — inside the **private** `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux` |

Inline-derivation grep (re-derived elsewhere without using the lemma?): **(none)** — the lemma is
the only place the sign+phase lift surjectivity is established; it is consumed exactly once,
immediately, by the private aux it was factored out of.

Call-sites signal: **K = 1 internal use only**, in the same file, feeding a `private` aux. Per the
verdicts reference this is the "possibly the wrong abstraction / could be inlined" pattern — a
**negative** composability/standalone-API signal. It is a once-used internal step, not a
reusable API surface.

## Composition check (Phase 6)

Can `mem_iUnion_image_liftToMixed_of_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Set.mem_iUnion.mpr ⟨signPattern x, …, (by … polarCoord …)⟩`
  - Mathlib decls available: `Complex.norm_mul_exp_arg_mul_I`, `mixedEmbedding.polarCoord(.symm)`,
    `mixedSpaceOfRealSpace`, `Set.mem_iUnion`, `Real.norm_eq_abs`, `abs_of_nonneg`/`abs_of_neg`.
  - Result: **fails as a ≤3-call composition.** The body genuinely *constructs* the witness
    (`choose θ … using exists_phase_mem_Icc_mul_exp`, builds `c` through `mixedCubeEquiv`, then
    `Prod.ext` + `funext` + a real-place sign case split + a complex-place phase rewrite). That is a
    real ≈28-line proof, not a `.symm`/`.trans`/one-call chain. The obstruction is the **project-local
    cube encoding** (`liftToMixed`/`mixedCubeEquiv`): mathlib's `polarCoord` gives the same *content*
    but in a different shape, so bridging it to the `⋃ ε, liftToMixed '' Icc` packaging is itself the
    work this lemma does.

Attempt 2: re-found the statement on `mixedEmbedding.polarCoord.symm` and `mixedSpaceOfRealSpace`.
  - Result: **partial** — this would replace, not compose; it changes the statement (Phase 4c,
    EXPENSIVE) and is a comment on the parent `def liftToMixed`, not an inlineable sketch for this lemma.

Conclusion: **NOT-COMPOSABLE** *as the lemma is currently stated* (it is bound to project-local
`liftToMixed`/`mixedCubeEquiv`). The *content* is mathlib-composable in spirit (polar + sign), but
only after re-founding the surrounding construction — which is a parent-def decision, not a
call-site inline.

## Verdict: `Chebotarev.mem_iUnion_image_liftToMixed_of_eq`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): no standalone/named form for the wrapper; underlying polar+sign fact
  is standard and ALREADY in mathlib (`Complex.norm_mul_exp_arg_mul_I`); the ambient argument is
  GRS/Debaene/Widmer Lipschitz-boundary lattice-counting, where such a fibre-lift is an internal step.
- Generality analysis (Phase 4): NEITHER maximally general NOR a clean specialisation — the statement
  is phrased in *project-local* vocabulary; Phase 4c flags a mathlib-idiomatic re-foundation on
  `mixedEmbedding.polarCoord`, but EXPENSIVE and really about the parent `def liftToMixed`.
- Mathlib search (Phase 5): user's exact form not in mathlib (head symbols project-local); building
  blocks present (`mixedEmbedding.polarCoord` / `polarSpaceCoord`, `mixedSpaceOfRealSpace`,
  `Complex.norm_mul_exp_arg_mul_I`) but not the cube-lift-union packaging.
- Composition check (Phase 6): NOT-COMPOSABLE as stated (≈28-line constructive proof bound to
  `liftToMixed`/`mixedCubeEquiv`); content is composable only after re-founding on `polarCoord`.
- Call sites (Phase 6.0): K = 1, same-file, feeding a `private` aux — "wrong abstraction / could be
  inlined" signal; no reuse, no external consumer.

**Rationale (1–2 paragraphs):**

This is **proof-specific scaffolding**, not a standalone mathlib candidate. Its conclusion is glued
to two project-defined objects — `liftToMixed K ψ ε` and (via `frontierCoverFamily` at the one call
site) the bespoke `mixedCubeEquiv` cube encoding — neither of which exists in mathlib. The genuine
*mathematical* content is the elementary sign-and-modulus / polar reconstruction of the mixed space,
and mathlib already owns that content twice over: pointwise as `Complex.norm_mul_exp_arg_mul_I` (on
which the project's own `exists_phase_mem_Icc_mul_exp` is literally built) and bundled as
`mixedEmbedding.polarCoord` / `polarSpaceCoord`. So the lemma is not contributing new mathematics;
it is *re-expressing known content* in the specific `⋃ ε, liftToMixed '' Icc 0 1` shape that the
GRS/Debaene Lipschitz-frontier-cover argument consumes — used exactly once, in the same file, by a
`private` aux it was factored out of.

It cannot be filed cleanly as NO-mathlib-has-it (mathlib has the *content*, not this exact
statement, and the ≤1-line specialisation gate fails — the cube-lift packaging is not a one-liner
off `polarCoord`), nor as NO-composable-from-mathlib (NOT-COMPOSABLE as stated: the ≈28-line proof
is real work bound to project objects, not a ≤3-call inline). The honest blocker is a **judgment
call about the parent definition `liftToMixed`**: if `liftToMixed` itself is never going to mathlib
(it is project cover-scaffolding), then this lemma trivially stays project-local and the question is
moot; if the *frontier-cover development* were ever upstreamed, the mathlib-native route is to
re-found it on `mixedEmbedding.polarCoord` (Phase 4c, EXPENSIVE), at which point this lemma is
replaced rather than ported. Either way the decl does not travel to mathlib on its own — and which
path applies depends on the fate of `liftToMixed`, which the skill cannot decide alone.

**Numbered questions (≤5):**

1. Is `liftToMixed` (and the whole `frontierCoverFamily` frontier-cover apparatus) intended ONLY as
   internal scaffolding for the Chebotarev lattice-point count, or is any of it meant to be
   upstreamed to mathlib? (If purely internal → this lemma stays project-local; close as
   NO-not-for-mathlib.)
2. If the cover *were* to be upstreamed, are you willing to re-found it on mathlib's existing
   `mixedEmbedding.polarCoord` / `polarSpaceCoord` change-of-variables (the idiomatic modulus+phase
   API) rather than the hand-rolled `liftToMixed` + `mixedCubeEquiv` cube encoding? (If yes → this
   lemma is *replaced*, not ported.)
3. Independently of the cover: would a **general** "fibre-surjectivity of `normAtAllPlaces`: every
   `x` with `normAtAllPlaces x = y` (`y ≥ 0`) is `mixedSpaceOfRealSpace y` adjusted by signs at real
   places and phases at complex places" lemma — stated against `mixedEmbedding.polarCoord`, with NO
   reference to cubes/`liftToMixed` — be useful to you? That *would* be a plausible mathlib addition
   to `…/CanonicalEmbedding/PolarCoord.lean`; this cube-shaped lemma is its bespoke specialisation.

**Next action:** user answers 1–3. Expected resolutions:
- Q1 = "internal only" → drop from mathlib consideration; keep as the project helper it is.
- Q3 = "yes, the polarCoord-stated general fibre lemma is useful" → file a *new* `/develop` item to
  state and prove that general lemma against `mixedEmbedding.polarCoord` (likely a real
  YES-add-as-is for `PolarCoord.lean`), and have this cube-lift lemma derive from it locally —
  rather than shipping `mem_iUnion_image_liftToMixed_of_eq` itself.

---

### Tooling notes for this run
- Local Lean build stale per task brief → Phase 0 `lake build` not run; reasoned from source
  (the decl is `sorry`-free and elaborates per the overview inventory).
- ChatGPT math MCP (Codex backend) **failed** on both attempts (`Reading additional input from
  stdin` / non-zero exit); recorded n/a. Standard-form question covered by WebSearch channels 2/3/10
  + the mathlib grep (Phase 5), which is the decisive channel here.
- `lean_loogle`/`lean_leansearch` (mathlib index) effectively unavailable offline; substituted with
  direct `grep` over `.lake/packages/mathlib/Mathlib/` (authoritative for "is the exact form / are
  the building blocks present").
