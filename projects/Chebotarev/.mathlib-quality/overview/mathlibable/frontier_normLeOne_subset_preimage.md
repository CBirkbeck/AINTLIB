# /mathlibable report — `Chebotarev.frontier_normLeOne_subset_preimage`

## Baseline (Phase 0)
- lake build:               not run (local build stale per task note; reasoning from source + mathlib source tree)
- decl `Chebotarev.frontier_normLeOne_subset_preimage`:
                            ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:597`
- qualified name:           **`Chebotarev.frontier_normLeOne_subset_preimage`** (inside `namespace Chebotarev`, opened at line 79; `end Chebotarev` at 673) — VERIFIED, matches the parsed name.
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` in `mixedSpace K`
  (the quantitative boundary regularity feeding the effective lattice-point count;
  Gun–Ramaré–Sivaraman §3.3 after Debaene). This file is a `ForMathlib/` helper.

---

## Statement (Phase 1)

`frontier_normLeOne_subset_preimage` states: for a number field `K`, the topological frontier of
`normLeOne K` (the norm-`≤ 1` slice of the fundamental cone inside `mixedSpace K`) is contained in
the `normAtAllPlaces`-preimage of the frontier of its `realSpace` image. In other words, writing
`f = normAtAllPlaces : mixedSpace K → realSpace K` and `S = f '' (normLeOne K)`,

  ∂(normLeOne K) ⊆ f⁻¹(∂S).

Mathematically this is the elementary point-set-topology fact `∂(f⁻¹ S) ⊆ f⁻¹(∂S)` for a continuous
`f`, applied after observing `normLeOne K = f⁻¹(S)` (because `normLeOne K` is saturated for the
fibres of `normAtAllPlaces` — it equals the preimage of its own image).

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K]` `[NumberField K]` — the number field (section variables of the file).

Hypotheses (Lean side): none beyond the variables (no explicit hypotheses).

Conclusion (math): `∂(normLeOne K) ⊆ normAtAllPlaces⁻¹(∂(normAtAllPlaces '' normLeOne K))`.

Conclusion (Lean):
`frontier (normLeOne K) ⊆ normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K)`.

**Proof body (2 lines):**
```lean
conv_lhs => rw [normLeOne_eq_preimage_image K]
exact (continuous_normAtAllPlaces K).frontier_preimage_subset _
```
i.e. rewrite `normLeOne K` as `normAtAllPlaces ⁻¹' (normAtAllPlaces '' normLeOne K)` using the
mathlib lemma `normLeOne_eq_preimage_image`, then apply the general mathlib lemma
`Continuous.frontier_preimage_subset` to the continuous map `normAtAllPlaces`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper lemma, a 2-line specialisation of a general topology lemma to one specific
continuous map; not a named theorem, not a new structure, not a `## Main results` entry (the file's
main results are `normLeOne_frontier_lipschitz_cover{,_mixedSpace,_index}`; this is plumbing for
the `_aux` lemma directly below it).

(Literature width run regardless; SMALL recorded for framing.)

## One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` — one-liner check **n/a**. (Note for context:
the *proof* is effectively one application after a `conv` rewrite, which is the relevant signal and
is captured in Phases 5–6.)

---

## Literature search (Phase 3)

The underlying mathematical content is the single elementary fact:

> For a continuous map `f : X → Y` of topological spaces and any `t ⊆ Y`,
> `frontier (f⁻¹ t) ⊆ f⁻¹ (frontier t)` (boundary = closure ∖ interior).

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | continuous map frontier preimage subset `f⁻¹` frontier topology general theorem        | partial | `∂(f⁻¹A) ⊆ f⁻¹(∂A)` for continuous f; only continuity needed | Standard point-set fact; texts give `cl(f⁻¹A)⊆f⁻¹(clA)` + `f⁻¹(intA)⊆int(f⁻¹A)` and subtract. (Leinster, Viro *Topoman* Ch.II §8, Orson point-set notes.) |
|  2 | WebSearch (general form)         | (same query, general-form framing) frontier = closure ∖ interior; minimal hypotheses   | yes  | continuity is the only hypothesis; equality needs f open/quotient | The subset direction is exactly "continuity"; no separation or finiteness needed. |
|  3 | WebSearch (named-after / aliases)| "boundary of preimage" / "frontier of preimage" continuous                              | yes (as folklore) | no person's name; it is unnamed folklore | Not a named theorem; it is a one-line exercise in every general-topology course. |
|  4 | ChatGPT MCP                      | "is `∂(f⁻¹ t) ⊆ f⁻¹(∂ t)` for continuous f standard; one-line proof; minimal hyp?"     | n/a  | —                   | **MCP down** in this environment (Codex stdin error on every call, as the task warned). Fact is elementary and independently confirmed by mathlib's own source (Phase 5). |
|  5 | Local references                 | `.mathlib-quality/references/` for "frontier"/"preimage"                                | n/a  | —                   | Source paper (Gun–Ramaré–Sivaraman) is about the *lattice-point count*, not this topology lemma; no refs dir entry bears on it. |
|  6 | nLab                             | "boundary of preimage" / closure & interior under continuous maps                       | n/a  | —                   | nLab has `closure`/`interior` behaviour under continuous maps but no dedicated page; not a categorical concept worth a page. |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project                   | —                                                                                       | n/a  | —                   | Not an algebraic-geometry concept (this is metric/point-set topology of the canonical embedding). |
|  9 | MathOverflow / MSE               | boundary of preimage under continuous map inclusion                                     | yes  | `∂f⁻¹(A) ⊆ f⁻¹(∂A)` for continuous f; standard MSE answer | Confirms it is textbook folklore; equality iff extra openness/quotient conditions. |
| 10 | recent arXiv (last 5 yr)         | —                                                                                       | n/a  | —                   | A 19th/20th-century point-set fact; no recent literature. |

### Literature summary (Phase 3)

Concept identified as: **boundary/frontier of a preimage under a continuous map** (unnamed
point-set-topology folklore; the inclusion `∂(f⁻¹A) ⊆ f⁻¹(∂A)`).
Sources agree on the standard form: **yes** — continuity is the only hypothesis for the subset
direction; X, Y, t fully arbitrary.
Most general standard form: `f : X → Y` continuous, `t ⊆ Y` arbitrary, `X, Y` arbitrary topological
spaces ⟹ `frontier (f⁻¹ t) ⊆ f⁻¹ (frontier t)`. Equality holds under stronger hypotheses (f an open
map, or a homeomorphism / quotient map).
Generality dimensions where the literature varies:
  - hypothesis on f: continuous (subset) … open map (equality) — the *subset* form is the maximal-
    generality continuous statement.
  - spaces/subset: always fully arbitrary.
Disagreement with the literature: **none**. The project lemma is the literature fact, specialised to
`f = normAtAllPlaces` and `t = normAtAllPlaces '' normLeOne K`.

---

## Generality analysis (Phase 4)

The project lemma is **not** the general statement — it is the general statement instantiated at one
specific continuous map. The relevant generality question is therefore not "can the project lemma be
weakened" but "does mathlib already hold the general form?" (Phase 5: yes).

Literature-standard form (from Phase 3): `Continuous f → frontier (f⁻¹ t) ⊆ f⁻¹ (frontier t)`,
`X Y` arbitrary, `t` arbitrary.

| # | Parameter / hypothesis            | Current Lean form                     | Literature-standard form        | Weaker form exists? | Reason |
|---|-----------------------------------|---------------------------------------|---------------------------------|---------------------|--------|
| 1 | the map                           | the *fixed* map `normAtAllPlaces`     | any continuous `f : X → Y`      | yes — DRAMATICALLY  | nothing about `normAtAllPlaces` is used except its continuity; the general form abstracts it away entirely |
| 2 | the set                           | the *fixed* set `normAtAllPlaces '' normLeOne K` | any `t ⊆ Y`          | yes                 | nothing about `normLeOne K` is used except that it equals `f⁻¹(its image)`, which holds for any set of the form `f⁻¹ S` |
| 3 | the spaces                        | `mixedSpace K` → `realSpace K`        | arbitrary topological spaces    | yes                 | no metric/finite-dimensional structure is used |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but, crucially, **the maximally general
form is itself already in mathlib** (Phase 5). So this is *not* a "generalise then add" situation:
generalising the project lemma reproduces an existing mathlib lemma verbatim. The number of
weakening axes is large (the map, the set, and the spaces all become arbitrary), and the fully
weakened statement = `Continuous.frontier_preimage_subset`, which exists.
Cost of restatement to the general form: n/a — the general form is not ours to add; mathlib has it.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1  | bundled hyps → typeclasses? | no | `Continuous` is already the right (term) hypothesis; the general mathlib lemma already uses it | — |
| 2  | sequences/metric → filters/topological? | no | already purely topological (closure/interior) | — |
| 3  | construction → universal property? | no | nothing constructed | — |
| 4  | subset-predicate → bundled substructure? | no | plain `Set` frontier inclusion | — |
| 5  | vector-space/metric → weaker typeclass? | no | already in arbitrary topological spaces in the general form | — |
| 6  | 1-categorical → higher-categorical? | no | n/a | — |
| 7  | concrete index → general algebraic structure? | no | n/a | — |

Modern idiom available: **no**. The general mathlib lemma `Continuous.frontier_preimage_subset` is
already the contemporary idiomatic form (term `Continuous` hypothesis, arbitrary spaces, `Set`
frontier). There is nothing to modernise.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities / typeclass-search paths introduced).

---

## Mathlib search-status (Phase 5)

Searched the actual mathlib source tree at
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/` (more authoritative than the
online index; the dedicated Loogle/LeanSearch MCP tools were not registered in this environment, and
the ChatGPT MCP was down — but a direct source grep settles the question definitively).

[A] Lean-Finder       n/a — MCP not available in this environment
[B] Loogle            n/a — MCP not registered; substituted by exhaustive grep of the mathlib tree (method [D])
[C] LeanSearch        n/a — MCP not registered; substituted by [D]
[D] Grep mathlib src  `grep -rn "frontier_preimage" .lake/packages/mathlib/Mathlib/` →
                      **HIT**: `Continuous.frontier_preimage_subset` at
                      `Mathlib/Topology/Continuous.lean:200`:
                      ```lean
                      theorem Continuous.frontier_preimage_subset (hf : Continuous f) (t : Set Y) :
                          frontier (f ⁻¹' t) ⊆ f ⁻¹' frontier t :=
                        diff_subset_diff (hf.closure_preimage_subset t)
                          (preimage_interior_subset_interior_preimage hf)
                      ```
                      Also found (related, preimage-direction): `IsOpenMap.preimage_frontier_subset_frontier_preimage`
                      and `IsOpenMap.preimage_frontier_eq_frontier_preimage` (Maps/Basic.lean:449,455 — the
                      *equality* under an open map, the stronger statement).
[E] Name pattern      grep for `frontier_normLeOne_subset_preimage` in mathlib → no hit (the
                      *specialisation* is not in mathlib, only the general lemma it instantiates).

Searched for both:
  - the user's current form (`frontier (normLeOne K) ⊆ …`) → not in mathlib as a named lemma.
  - the literature-standard / general form (`Continuous f → frontier (f⁻¹ t) ⊆ f⁻¹ frontier t`) →
    **in mathlib as `Continuous.frontier_preimage_subset`** (`Mathlib/Topology/Continuous.lean:200`).

Also confirmed the two rewrite ingredients are mathlib, in the very file the project imports
(`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne`):
  - `normLeOne_eq_preimage_image` — `NormLeOne.lean:175`.
  - `continuous_normAtAllPlaces` — used at `NormLeOne.lean:682,797`.

Concluded: **found in mathlib as `Continuous.frontier_preimage_subset`; strictly more general form
(the project lemma is the specialisation to `f = normAtAllPlaces`, `t = normAtAllPlaces '' normLeOne K`).**
The specialisation follows from the mathlib lemma in ≤2 lines (one rewrite + one application).

---

## Composition check (Phase 6)

### Call sites — `Chebotarev.frontier_normLeOne_subset_preimage`

Internal use count: **1** (within the project, excluding the declaring file: **0**).
External-to-file callers: **0** distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ForMathlib/NormLeOneLipschitz.lean:609 | `refine (frontier_normLeOne_subset_preimage K).trans ?_` (in `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`, the `private` lemma directly below it) |

Inline-derivation grep: the only consumer is the adjacent `_aux` lemma; no other site re-derives it.

Signal: K = 1, and the single use is in the **same file**, the immediately following `private` lemma.
This is the "possibly the wrong abstraction — could be inlined" pattern. There are no external or
downstream consumers, and the body is itself a 2-line specialisation. The call-site pattern reinforces
NO (inline at the one site).

### Composition check (Phase 6)

Can `frontier_normLeOne_subset_preimage` be derived from mathlib in ≤3 chained calls?

Attempt 1: `by rw [normLeOne_eq_preimage_image]; exact (continuous_normAtAllPlaces K).frontier_preimage_subset _`
  - Mathlib decls used: `normLeOne_eq_preimage_image` (NormLeOne.lean:175),
    `Continuous.frontier_preimage_subset` (Continuous.lean:200), `continuous_normAtAllPlaces`
    (NormLeOne.lean).
  - Result: **succeeds** — this IS the project proof verbatim (1 rewrite + 1 application).
  - Notes: every ingredient is a mathlib lemma; nothing project-specific is invented.

Conclusion: the result is obtained by **specialising one general mathlib theorem after a single
mathlib rewrite**. Per the verdict-doc boundary, because mathlib holds the *general theorem* and the
project lemma is its ≤2-line specialisation to a fixed map/set, this is **NO-mathlib-has-it** (mathlib
has the result in strictly-more-general form), not a fresh `NO-composable` building-block assembly.
Either way the action is identical: do not add to mathlib; inline at the one call site.

---

## Verdict: `Chebotarev.frontier_normLeOne_subset_preimage`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): the content is the unnamed point-set fact `∂(f⁻¹t) ⊆ f⁻¹(∂t)` for
  continuous `f`; continuity is the only hypothesis; spaces/set arbitrary.
- Generality analysis (Phase 4): STRICTLY NARROWER than the general form — but the general form is
  already in mathlib, so generalising reproduces an existing lemma (no modernisation available).
- Mathlib search (Phase 5): **found in mathlib as `Continuous.frontier_preimage_subset`**
  (`Mathlib/Topology/Continuous.lean:200`), the strictly more general form; the two rewrite
  ingredients (`normLeOne_eq_preimage_image`, `continuous_normAtAllPlaces`) are also mathlib.
- Composition check (Phase 6): the project proof = 1 mathlib rewrite + 1 application of the general
  mathlib lemma; sole consumer is the adjacent private `_aux` lemma (K = 1, in-file).

**Rationale:**

The general theorem this lemma instantiates — `Continuous f → frontier (f⁻¹ t) ⊆ f⁻¹ (frontier t)`
— is already in mathlib as `Continuous.frontier_preimage_subset` (`Mathlib/Topology/Continuous.lean:200`),
at exactly the maximal generality the literature uses (only continuity; arbitrary spaces and set).
The project lemma is that theorem specialised to `f = normAtAllPlaces` and
`t = normAtAllPlaces '' normLeOne K`, reached by first rewriting `normLeOne K` into preimage form via
the mathlib lemma `normLeOne_eq_preimage_image`. Mathlib's own `NormLeOne.lean` already performs the
*identical composition pattern* for the sibling closure/interior statements — `closure_normLeOne_subset`
(line 794) uses `normLeOne_eq_preimage` + `Continuous.closure_preimage_subset`, and
`subset_interior_normLeOne` (line 678) uses `normLeOne_eq_preimage` +
`preimage_interior_subset_interior_preimage` — which makes the frontier sibling a textbook
follow-in-≤2-lines specialisation, not new content.

There is no generalisation worth doing (Phase 4c finds no modern-idiom improvement; the general form
is already idiomatic mathlib), and there is no novelty: the only thing "added" over mathlib is the
choice of `f` and `t`, plus one rewrite. The single consumer is the private `_aux` lemma two lines
down; inlining there costs one line. This is a clean `NO-mathlib-has-it`.

**WHY not (refactor-actionable):**
Mathlib already has the result in strictly-more-general form: `Continuous.frontier_preimage_subset`
(`Mathlib/Topology/Continuous.lean:200`). The project's form is the specialisation
`f := normAtAllPlaces`, `t := normAtAllPlaces '' normLeOne K`, obtained after rewriting `normLeOne K`
to preimage form with the mathlib lemma `normLeOne_eq_preimage_image` (`Mathlib/NumberTheory/
NumberField/CanonicalEmbedding/NormLeOne.lean:175`).

Existing mathlib decl:        `Continuous.frontier_preimage_subset`
Located at:                   `Mathlib/Topology/Continuous.lean:200`
Supporting mathlib decls:     `normLeOne_eq_preimage_image` (`…/NormLeOne.lean:175`),
                              `continuous_normAtAllPlaces` (`…/NormLeOne.lean`, used at 682/797).

Our form follows in ≤2 lines (this is the existing proof):
```lean
example (K : Type*) [Field K] [NumberField K] :
    frontier (normLeOne K) ⊆
      normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K) := by
  rw [normLeOne_eq_preimage_image K]
  exact (continuous_normAtAllPlaces K).frontier_preimage_subset _
```

Call sites in our project (from Phase 6.0): **1** — `NormLeOneLipschitz.lean:609`
(`frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`), and **0** outside the declaring file.

Refactor plan: at the single call site (line 609), replace
`(frontier_normLeOne_subset_preimage K).trans ?_` with the inlined two-step specialisation — e.g.
open the `_aux` proof with `rw [normLeOne_eq_preimage_image K]` and lead with
`((continuous_normAtAllPlaces K).frontier_preimage_subset _).trans ?_`, then delete the standalone
`frontier_normLeOne_subset_preimage` theorem. No argument-order subtleties (it is applied via `.trans`
in exactly one place). Sorry-free; safe for the `lane:cleanup` fleet to inline (the proof axioms are
unchanged — only `propext`/`Classical.choice`/`Quot.sound` are involved transitively).

**Caveat for the human:** this is a `ForMathlib/` file the author earmarked for upstreaming. The
*correct* upstream move is **not** to add this specialised wrapper to mathlib — it is to keep using
`Continuous.frontier_preimage_subset` directly at the (one) call site. If the surrounding development
`normLeOne_frontier_lipschitz_cover{,_mixedSpace,_index}` is itself upstreamed, this helper should be
inlined as part of that PR rather than shipped as a named lemma.

Next action: delete `frontier_normLeOne_subset_preimage`; inline the 2-line specialisation at
`NormLeOneLipschitz.lean:609` (or leave as a local `have` inside the `_aux` proof).

---

## Next step

Delete `Chebotarev.frontier_normLeOne_subset_preimage` and inline the two-step specialisation of
`Continuous.frontier_preimage_subset` (after the `normLeOne_eq_preimage_image` rewrite) at its single
call site `NormLeOneLipschitz.lean:609`. Do not add this wrapper to mathlib — mathlib already has the
general lemma.
