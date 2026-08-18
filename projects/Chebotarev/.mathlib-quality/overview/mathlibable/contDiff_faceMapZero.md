# /mathlibable report — `Chebotarev.contDiff_faceMapZero`

### Baseline (Phase 0)
- lake build:               not re-run (local build is stale per task brief); reasoning from source statement.
- decl `Chebotarev.contDiff_faceMapZero`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:152`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the
  Gun–Ramaré–Sivaraman §3.3 (after Debaene) boundary-cell input for the effective lattice-point
  count, feeding Widmer/Lang (GTM 110, Ch. V §2).
- qualified name:            namespace `Chebotarev`, base `contDiff_faceMapZero`
  (confirmed: `namespace Chebotarev` at line 79, no inner namespace; `end Chebotarev` at line 673).
  The prompt's parsed `Chebotarev.contDiff_faceMapZero` is CORRECT.

---

### Statement (Phase 1)

`contDiff_faceMapZero` states: for a number field `K`, the map `faceMapZero K : ({w // w ≠ w₀} → ℝ)
→ realSpace K` is continuously differentiable (`ContDiff ℝ 1`).

Here `faceMapZero K c = expMapBasis (fun w ↦ if w = w₀ then 0 else c ⟨w, _⟩)` (line 137): it is the
mathlib map `expMapBasis` precomposed with the "slot map" that places `0` in the distinguished
`w₀`-coordinate and the cube-coordinate `c w` in every other slot. Geometrically it parametrizes the
`expMapBasis`-image of the `w₀`-face `{x | x w₀ = 0}` of the box `paramSet K`. The lemma asserts this
parametrization is `C¹` — the regularity needed to later conclude (via
`exists_lipschitzWith_comp_clampUnit`) that the face is a Lipschitz image of the unit cube.

In words: a `C¹` map (`expMapBasis`) composed with an affine/coordinate-selecting slot map is `C¹`.

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K] [NumberField K]` — a number field (so `realSpace K = InfinitePlace K → ℝ`
  is a finite-dim'l real normed space, and `expMapBasis`, `w₀` are available from mathlib).

Hypotheses (Lean side): none (besides the `NumberField K` instance).

Conclusion (math): the `w₀`-face parametrization `faceMapZero K` is continuously differentiable.

Conclusion (Lean): `ContDiff ℝ 1 (faceMapZero K)`.

Proof body (4 lines, line 152–156):
```lean
refine (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_)
by_cases hw : w = w₀
· simpa only [dif_pos hw] using contDiff_const
· simpa only [dif_neg hw] using contDiff_apply ℝ ℝ _
```
i.e. `ContDiff.comp` of `contDiff_expMapBasis` (the project's `C¹`-ness of `expMapBasis`) with the
slot map, the slot map shown `C¹` coordinatewise by `contDiff_pi` + a two-case split
(`contDiff_const` in the pinned `w₀` slot, `contDiff_apply` — coordinate projection — elsewhere).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `ForMathlib/` helper lemma feeding the boundary-cover construction; not a `## Main
results` entry, not named after a person/place, introduces no new structure. Its *subject*
`faceMapZero` is itself a bespoke project def. (Lit width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` — the one-line `def` check is n/a. (For reference: the companion `def faceMapZero`
at line 137 is a ~2-line `def`, but that is a separate declaration and out of scope here.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                            | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-----------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "smoothness of composition of C¹ functions chain rule continuously differentiable standard"    | yes  | "compositions of composable C¹-maps are C¹" (chain rule)        | Wikipedia *Smoothness* / *Chain rule*; USTC Lec 3 notes — foundational |
|  2 | WebSearch (general form)         | "function into product space R^n is C¹ iff each coordinate component is C¹"                     | yes  | a map into a (finite) product is C¹ ⟺ each component is C¹       | standard multivariable-calculus fact; arXiv:1409.6195 (restricted products) for the general LCS version |
|  3 | WebSearch (named technique / mathlib) | "mathlib4 contDiff_pi contDiff_apply ContDiff.comp coordinate smoothness"                 | yes  | `ContDiff.comp` (comp of Cⁿ is Cⁿ); `contDiff_pi` (pi criterion) | leanprover-community mathlib4 docs — the exact API used by the proof |
|  4 | WebSearch (coordinate maps)      | "coordinate projection / evaluation map smooth linear continuous differentiable Pi type"       | yes  | coordinate projections are smooth; smoothness tested coordinatewise | nLab *smooth map*; ANU/UCLA DG notes — projections are linear ⟹ smooth |
|  5 | ChatGPT MCP                      | standard-form + generality + "wrapper vs standalone" (3-part)                                   | n/a  | —                                                               | MCP down per task brief (fallbacks used: channels 1–4, 6, 10) |
|  6 | Local references                 | `.mathlib-quality/references/` for the project                                                  | n/a  | (directory absent)                                              | `projects/Chebotarev/.mathlib-quality/references/` does not exist |
|  7 | nLab                             | "smooth map coordinatewise / composition" (fetched ncatlab.org/nlab/show/smooth+map)           | yes  | "suffices to take π to range over the m coordinate projections" | nLab confirms the coordinate-wise criterion = mathlib `contDiff_pi`; composition closure assumed standard |
|  8 | nCatLab (categorical)            | (same page — Diff as a category, smooth maps as morphisms)                                      | n/a  | —                                                               | not a categorical result; it is an application of basic calculus |
|  9 | Stacks Project (alg geom)        | —                                                                                              | n/a  | —                                                               | not an algebraic-geometry concept |
| 10 | MathOverflow / Math.SE           | (folded into #1–#4) chain rule + coordinatewise smoothness                                      | yes  | folklore: comp of C¹ is C¹; C¹ tested per-coordinate            | corroborated across the standard DG lecture notes above |
| 11 | recent arXiv (last 5y)           | "counting ideals ray classes Lipschitz boundary cube parametrization C¹ frontier number field" | yes  | GRS/Debaene/Widmer Lipschitz-boundary lattice counting          | arXiv:1611.10103, 2411.13522, 2203.00389 — the *application context*; the face-parametrization `faceMapZero` is a bespoke formalisation artifact, NOT a named literature object |

The protocol passed: WebSearch ran 4 queries at distinct generality levels (chain-rule / pi-criterion
/ mathlib-API / coordinate-projection); ChatGPT MCP recorded n/a with reason (down); local refs n/a
(absent); nLab checked (hit); Stacks/nCatLab n/a with reason; MathOverflow folded in; arXiv checked
(hit — application context only).

### Literature summary (Phase 3)

Concept identified as: an instance of **two foundational calculus facts**:
  (a) the **chain rule** — "the composition of `C¹` maps is `C¹`" (`ContDiff.comp`), and
  (b) the **coordinatewise criterion** — "a map into a finite product is `C¹` iff each coordinate is
      `C¹`" (`contDiff_pi`), with the coordinate slots here being either a constant (`contDiff_const`)
      or a coordinate projection (`contDiff_apply`, which is smooth because projections are linear).
Sources agree on the standard form: **yes**. Both (a) and (b) are universally stated and treated as
elementary; nLab states the coordinate criterion verbatim ("it suffices to take π to range over the m
coordinate projections").
Most general standard form: (a) holds for `Cⁿ` maps between Banach spaces; (b) holds for maps into an
arbitrary (finite, or suitable) product of Banach spaces.
Generality dimensions where the literature varies: regularity (`C¹`↔`Cⁿ`↔`C∞`), and the ambient
spaces (`ℝⁿ`↔Banach↔locally-convex). None of this bears on the present lemma, because the lemma is
**not a general statement at all** — it is `ContDiff ℝ 1 (faceMapZero K)`, a smoothness assertion
about one *specific project-defined map*.
Disagreement with the literature: none. The literature has no object called "faceMapZero" or any
"`C¹`-ness of the `w₀`-face parametrization" — that is a formalisation-internal artifact of this
particular frontier-cover construction.

---

### Generality analysis — `Chebotarev.contDiff_faceMapZero`

Literature-standard form (from Phase 3): there is no general literature statement to match — the
lemma's subject `faceMapZero K` is a bespoke project definition. The closest *reusable* statement in
the vicinity is "the **mathlib** object `expMapBasis` is `C¹`" (the project's separate sibling
`contDiff_expMapBasis`), of which `contDiff_faceMapZero` is a downstream precomposition.

| # | Parameter / hypothesis      | Current Lean form                        | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|------------------------------------------|--------------------------------------------|---------------------|---------------------------------|
| 1 | `[NumberField K]`           | number field (fixes `realSpace`, `w₀`, `expMapBasis`) | none — the statement is *about a number-field-specific map* | NO | the whole point is the `expMapBasis`/`w₀` of *this* `K`; nothing to weaken — it is maximally specific, not maximally general |
| 2 | regularity `ContDiff ℝ 1`   | `C¹`                                     | `Cⁿ` / `C∞` (the comp+pi facts hold for any `n`) | yes (vacuously)     | `expMapBasis` is in fact `C∞`; but the project only needs `C¹` (Lipschitz input), and this is a leaf application, not a reusable lemma to over-generalise |
| 3 | subject `faceMapZero K`     | a fixed bespoke face-parametrization     | n/a — not a literature object              | NO | one cannot "generalise" the subject without deleting the lemma; it is glue *about a specific def* |

### Generality verdict (Phase 4b)

The current form is: **NEITHER maximally general NOR meaningfully generalisable** — it is a maximally
*specific* statement about a project-defined map. There is no literature-standard general form to aim
at (the general facts it instantiates — `ContDiff.comp`, `contDiff_pi` — are already in mathlib).
Number of weakening opportunities found: **0** that produce a mathlib-shaped general lemma (row 2's
`C¹`→`Cⁿ` is not a generalisation of *this* statement, just of the ambient facts it uses).
Proposed restatement: **none** — this decl is not a candidate for restate-and-upstream. The
upstreamable kernel in this file is the *sibling* `contDiff_expMapBasis` (a `ContDiff` fact about the
mathlib object `expMapBasis`), assessed separately; even that is a `fun_prop` derivation from
`hasFDerivAt_expMapBasis`, which mathlib already has.
Cost of restatement: **n/a**.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation                          | Mathlib downstream |
|----|-----------------------------------------------------------------------------------|----------|--------------------------------------------------|--------------------|
|  1 | bundled-hypothesis preamble → typeclass/instance?                                 | no       | hypotheses are already mathlib typeclasses       | — |
|  2 | sequences/metric → filters/topological?                                           | no       | `ContDiff` is already the right notion           | — |
|  3 | construct object → universal-property class?                                      | no       | nothing constructed; it is a `Prop`              | — |
|  4 | set-with-predicate → bundled substructure?                                        | no       | no substructure involved                         | — |
|  5 | field/metric-specific → weaken typeclass hierarchy?                               | no       | the `ℝ`/number-field/`expMapBasis` data is essential to the statement's subject | — |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a                                              | — |
|  7 | concrete index → arbitrary additive/ordered structure?                            | no       | the index `{w // w ≠ w₀}` is fixed by the construction | — |

### Modern-idiom verdict (Phase 4c)
Modern idiom available: **no**. The proof is *already* in the modern mathlib idiom — `ContDiff.comp`
+ `contDiff_pi`/`contDiff_apply`/`contDiff_const`, every one of those `@[fun_prop]`-tagged. There is
no contemporary reformulation that improves organisation: the statement is a single-use smoothness
fact about a bespoke map, and the reusable engine it leans on (`expMapBasis` differentiability) is
already upstream as `hasFDerivAt_expMapBasis`.

---

### Diamond / defeq risk — Phase 4.5
n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search
paths). [The dependency `def faceMapZero` is a separate decl; its risk is out of scope here.]

---

### Mathlib search-status: `Chebotarev.contDiff_faceMapZero`

[A] Lean-Finder       n/a (deferred tool not available in this env)
[B] Loogle            n/a (`lean_loogle` not available in this env, per task brief); substituted by
                      direct mathlib-src grep [D]
[C] LeanSearch        n/a (`lean_leansearch` not available); substituted by WebSearch channel 3 +
                      mathlib4 docs (`Analysis/Calculus/ContDiff/Operations.html`)
[D] Grep mathlib src  `contDiff_pi`, `contDiff_apply`, `ContDiff.comp`, `contDiff_const`, `faceMapZero`,
                      `expMapBasis`, `hasFDerivAt_expMapBasis` over `.lake/packages/mathlib/Mathlib/`
[E] Name pattern      grep for `faceMapZero`, `contDiff_faceMap*`, any `*face*` ContDiff in mathlib → none

Searched for both:
  - the user's current form ("`C¹`-ness of `faceMapZero K`") — **not in mathlib, and cannot be**:
    `faceMapZero` is a project-local def (grep of `.lake/.../mathlib/` for `faceMapZero` → 0 hits),
    so no mathlib lemma can mention it;
  - the building blocks / re-aim target:
      · `ContDiff.comp` (comp of `Cⁿ` is `Cⁿ`) → **FOUND**
        `Mathlib/Analysis/Calculus/ContDiff/Comp.lean:155`;
      · `contDiff_pi` (map into pi is `Cⁿ` ⟺ each coord is) → **FOUND**
        `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:112` (with `@[fun_prop]` `contDiff_pi'` at 116);
      · `contDiff_apply` (coordinate projection is `Cⁿ`) → **FOUND**, `@[fun_prop]`,
        `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:145`;
      · `contDiff_const` (constants are `Cⁿ`) → **FOUND**, `Mathlib/Analysis/Calculus/ContDiff/Basic.lean:103`;
      · differentiability of the subject map `expMapBasis` → **FOUND in mathlib** as
        `hasFDerivAt_expMapBasis` (`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:580`,
        with `fderiv_expMapBasis` at :576). Note: mathlib gives the *Fréchet derivative everywhere*,
        but does NOT state the `ContDiff ℝ 1` packaging — that packaging is the project's *separate*
        `contDiff_expMapBasis` (line 126), proved by `fun_prop`.

Concluded: **"found building blocks; composition would yield our form."** Mathlib has every glue
primitive (`ContDiff.comp`, `contDiff_pi`, `contDiff_apply`, `contDiff_const`, all `@[fun_prop]`) and
the derivative of the one non-trivial ingredient `expMapBasis` (`hasFDerivAt_expMapBasis`). It does
NOT — and structurally cannot — have a lemma about the project-local `faceMapZero`.

---

### Call sites — `Chebotarev.contDiff_faceMapZero`

Internal use count: **2** (within the project; NOT counting a declaration's own header line).
External-to-file callers: **0 distinct files**. Both uses are *inside the declaring file itself*
(`NormLeOneLipschitz.lean`).

| Caller file:line                       | Usage pattern (one-line excerpt)                                                |
|----------------------------------------|----------------------------------------------------------------------------------|
| NormLeOneLipschitz.lean:298            | `obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)` |
| NormLeOneLipschitz.lean:540            | `obtain ⟨B₀, hB₀⟩ := hbd _ (contDiff_faceMapZero K).continuous`                    |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none found) — the lemma is referenced exactly at its two intended consumers (Lipschitz-constant
    extraction at 298; continuity-for-boundedness at 540), both for the `faceMapZero` family.

Composability signal: **K = 2 internal uses, both confined to the single declaring file, 0 external
callers.** Per the call-sites table this is a private-helper / single-file-glue signal leaning toward
NO-composable — it exists to package the same 4-line `comp`/`pi` composition once for the `w₀`-face,
so the two downstream consumers can write `contDiff_faceMapZero K` instead of re-deriving it.

---

### Composition check (Phase 6)

Can `contDiff_faceMapZero` be derived from mathlib (+ the file's own `contDiff_expMapBasis`) in ≤3
chained calls?

Attempt 1 (the source proof itself — `ContDiff.comp` of two `@[fun_prop]`-provable facts):
```lean
example (K : Type*) [Field K] [NumberField K] : ContDiff ℝ 1 (faceMapZero K) :=
  (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ by
    by_cases hw : w = w₀
    · simpa only [dif_pos hw] using contDiff_const
    · simpa only [dif_neg hw] using contDiff_apply ℝ ℝ _)
```
  - Mathlib decls used: `ContDiff.comp`, `contDiff_pi`, `contDiff_apply`, `contDiff_const` (plus the
    file's `contDiff_expMapBasis`, itself a `fun_prop` one-liner).
  - Result: **succeeds** — this *is* the body (one `.comp` call; the inner `pi` discharge is the
    coordinatewise `dif`-split). By the Phase-6 heuristics, `(contDiff_expMapBasis K).comp (…)` is the
    `Foo.bar (Bar.baz hx)` "one function call" pattern = composable.

Attempt 2 (fully automated, modulo the slot-map `dif`-reduction):
```lean
example (K : Type*) [Field K] [NumberField K] : ContDiff ℝ 1 (faceMapZero K) := by
  unfold faceMapZero
  fun_prop                 -- contDiff_pi'/apply/const are @[fun_prop]; needs contDiff_expMapBasis in scope
```
  - Because `contDiff_pi'`, `contDiff_apply`, `contDiff_const` are all `@[fun_prop]` and
    `contDiff_expMapBasis` is the `fun_prop`-proved smoothness of the head map, the composition is
    exactly what `fun_prop` is designed to close (the explicit `by_cases` in the source is just
    discharging the `dite` in the slot map by hand). The heavy lifting is one `comp`; the rest is the
    automation tactic.

Conclusion: **COMPOSABLE.** The result is `ContDiff.comp` of `contDiff_expMapBasis` with a
coordinatewise-smooth slot map (`contDiff_pi` + `contDiff_apply`/`contDiff_const`), all four mathlib
pieces `@[fun_prop]`-tagged. This is a textbook one-`comp` composition, not new mathematical content.

---

## Verdict: `Chebotarev.contDiff_faceMapZero`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the statement instantiates two foundational calculus facts — the
  chain rule ("comp of `C¹` is `C¹`") and the coordinatewise criterion ("map into a product is `C¹`
  iff each coordinate is"); nLab states the latter verbatim. The *subject* `faceMapZero` is a bespoke
  formalisation artifact with no literature object.
- Generality analysis (Phase 4): the statement is maximally *specific* (a `ContDiff` fact about one
  project-defined map), with 0 weakenings that yield a mathlib-shaped general lemma; Phase 4c found
  the proof already in the modern `@[fun_prop]` idiom.
- Mathlib search (Phase 5): "found building blocks" — `ContDiff.comp`
  (`…/ContDiff/Comp.lean:155`), `contDiff_pi` (`…/ContDiff/Operations.lean:112`), `contDiff_apply`
  (`…/Operations.lean:145`), `contDiff_const` (`…/ContDiff/Basic.lean:103`), and the subject's
  derivative `hasFDerivAt_expMapBasis` (`…/NormLeOne.lean:580`). No lemma about the project-local
  `faceMapZero` exists or can exist in mathlib.
- Composition check (Phase 6): COMPOSABLE — one `ContDiff.comp` of two `@[fun_prop]`-provable facts;
  the whole 4-line body reduces to `unfold faceMapZero; fun_prop` with `contDiff_expMapBasis` in scope.

**Rationale:**

`contDiff_faceMapZero` is a `ContDiff ℝ 1` assertion *about a project-specific definition*,
`faceMapZero K` — the `w₀`-face parametrization built as `expMapBasis ∘ (slot map)`. Because
`faceMapZero` is a bespoke artifact of this one frontier-cover construction (grep of the mathlib tree
returns zero hits), mathlib **cannot** have this exact lemma, and the lemma is **not a candidate to
upstream as-is**: you would never add `faceMapZero` to mathlib, so its smoothness lemma cannot go
either. What the lemma actually does is glue two well-known, already-in-mathlib facts — the chain rule
(`ContDiff.comp`) and the pi-criterion (`contDiff_pi` with `contDiff_apply`/`contDiff_const`) — onto
the smoothness of the *mathlib* head map `expMapBasis`. Every one of those four mathlib pieces is
`@[fun_prop]`-tagged, and `expMapBasis`'s derivative is itself in mathlib
(`hasFDerivAt_expMapBasis`); the 4-line proof is a single `.comp` whose remainder is the routine
coordinatewise `dite`-split, equivalently `unfold faceMapZero; fun_prop`. That is a composition of
existing primitives, not new content.

The call-sites evidence reinforces NO-composable: the lemma has **2 uses, both inside its own
declaring file** (lines 298, 540), **0 external callers**, no inline re-derivation elsewhere — a
single-file helper that packages the same composition for the `w₀`-face so its two local consumers
(Lipschitz-constant extraction and continuity-for-boundedness) can name it. It is the right *local*
abstraction, but it is not a mathlib-shaped contribution. The genuinely reusable kernel in this
vicinity is the *sibling* `contDiff_expMapBasis` — the `ContDiff` packaging of the mathlib object
`expMapBasis` — and even that is a `fun_prop` derivation from the already-upstream
`hasFDerivAt_expMapBasis`; it is a separate declaration and out of scope here.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the lemma is a one-`comp` composition over the project def
`faceMapZero` (so it can never *be* in mathlib, only inlined where `faceMapZero`'s smoothness is
needed).

Mathlib building blocks (qualified names + paths):
- `ContDiff.comp` — `Mathlib/Analysis/Calculus/ContDiff/Comp.lean:155` (comp of `Cⁿ` maps is `Cⁿ`).
- `contDiff_pi` / `contDiff_pi'` — `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:112` / `:116`
  (`@[fun_prop]`; a map into a pi type is `Cⁿ` iff each coordinate is).
- `contDiff_apply` — `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:145` (`@[fun_prop]`; a
  coordinate projection is `Cⁿ`).
- `contDiff_const` — `Mathlib/Analysis/Calculus/ContDiff/Basic.lean:103` (constants are `Cⁿ`).
- `hasFDerivAt_expMapBasis` — `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:580`
  (the differentiability of the head map `expMapBasis`, already upstream).
- (project-local: `contDiff_expMapBasis`, line 126 — the `ContDiff` packaging of `expMapBasis`, a
  `fun_prop` one-liner; itself a separate `/mathlibable` subject, not this decl.)

Composition sketch (the source body; ≤3 mathlib calls + the slot-map `dite`-split):
```lean
(contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ by
  by_cases hw : w = w₀
  · simpa only [dif_pos hw] using contDiff_const
  · simpa only [dif_neg hw] using contDiff_apply ℝ ℝ _)
-- equivalently:  by unfold faceMapZero; fun_prop   (with contDiff_expMapBasis available)
```

Call sites in the project (from Phase 6.0): **K = 2**, both in `NormLeOneLipschitz.lean` (lines 298,
540), 0 external.

Refactor plan (this is a keep-local / do-not-PR recommendation, NOT a delete-from-the-library
recommendation — `main` keeps the helper exactly as the producer wrote it; the point is it should not
be queued for a mathlib PR):
- Do **not** open a mathlib PR for `contDiff_faceMapZero`. Its subject `faceMapZero` is project-local;
  the reusable content (`expMapBasis` smoothness) is already upstream (`hasFDerivAt_expMapBasis`), and
  the glue is `ContDiff.comp` + the `@[fun_prop]` pi-API.
- It is a perfectly good *project-internal* helper as written: 2 consumers in-file, both naming it
  rather than re-deriving — keep it.
- Optional in-place golf (statement unchanged; a cleanup-lane concern, not mathlibable): the body
  could collapse to `by unfold faceMapZero; fun_prop` once `contDiff_expMapBasis` is in scope, since
  `contDiff_pi'`/`contDiff_apply`/`contDiff_const` are `@[fun_prop]`. Both call sites (298, 540) are
  unaffected — the lemma's type is identical.
- Separately and out of scope here: if anything from this file is upstreamed, the candidate is the
  *sibling* `contDiff_expMapBasis` (a `ContDiff` fact about the mathlib object `expMapBasis`) — assess
  that on its own; note even it largely duplicates `hasFDerivAt_expMapBasis` via `fun_prop`.

Next action: keep `contDiff_faceMapZero` project-local (a fine `ForMathlib/` *internal* helper);
optionally golf to `unfold faceMapZero; fun_prop`. Do not queue it for a mathlib PR.

---

## Next step

Keep the lemma project-local; do not PR to mathlib. It is a `ContDiff` fact about the project-defined
`faceMapZero`, hence not upstreamable as-is; its content is `ContDiff.comp` of the already-upstream
smoothness of `expMapBasis` (`hasFDerivAt_expMapBasis`) with the `@[fun_prop]` pi/coordinate API
(`contDiff_pi`, `contDiff_apply`, `contDiff_const`). Optionally golf the proof to
`unfold faceMapZero; fun_prop`. If any single thing from this file is worth upstreaming, it is the
*sibling* `contDiff_expMapBasis`, assessed separately.
