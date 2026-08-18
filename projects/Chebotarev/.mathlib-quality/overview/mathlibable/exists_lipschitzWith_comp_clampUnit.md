# /mathlibable report — `Chebotarev.exists_lipschitzWith_comp_clampUnit`

### Baseline (Phase 0)
- lake build:               not re-run (local build is stale per task brief); reasoning from source statement.
- decl `Chebotarev.exists_lipschitzWith_comp_clampUnit`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:115`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the
  Gun–Ramaré–Sivaraman §3.3 boundary-cell input for the effective lattice-point count.
- qualified name:            namespace `Chebotarev`, base `exists_lipschitzWith_comp_clampUnit`
  (confirmed: `namespace Chebotarev` at line 79, no inner namespace; `end Chebotarev` at line 673).

---

### Statement (Phase 1)

`exists_lipschitzWith_comp_clampUnit` states: if `f : (ι → ℝ) → (κ → ℝ)` is continuously
differentiable (`ContDiff ℝ 1`), with `ι, κ` finite, then there is a constant `M : ℝ≥0` such
that `f ∘ clampUnit ι` is globally `M`-Lipschitz on all of `ι → ℝ`. Here `clampUnit ι` is the
coordinatewise retraction onto the unit cube `Icc (0:ι→ℝ) 1` (each coordinate via `Set.projIcc 0 1`).

In words: a `C¹` map precomposed with the clamp onto the unit cube is globally Lipschitz. The
clamp's image is the compact convex cube, on which `f` is Lipschitz; off the cube the clamp is
constant in the saturated directions, so no new variation is introduced.

Variables / typeclasses (Lean side):
- `ι κ : Type*`, `[Fintype ι] [Fintype κ]` — finite index types (so `ι→ℝ`, `κ→ℝ` are
  finite-dim'l real normed spaces with the sup metric).
- `f : (ι → ℝ) → κ → ℝ` — the map.

Hypotheses (Lean side):
- `hf : ContDiff ℝ 1 f` — `f` is `C¹`.

Conclusion (math): `∃ M ≥ 0`, the composite `f ∘ (clamp onto [0,1]^ι)` is `M`-Lipschitz on the
whole space.

Conclusion (Lean): `∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι)`.

Proof body (4 lines): `hf.locallyLipschitz.locallyLipschitzOn (s := Icc 0 1)` →
`.exists_lipschitzOnWith_of_compact isCompact_Icc` gives `LipschitzOnWith M f (Icc 0 1)`; then
for any `c d`, `clampUnit` lands in the cube so `hM` applies, and the result is glued with the
fact that `clampUnit` is `1`-Lipschitz (`lipschitzWith_clampUnit`) via `.trans` + `gcongr`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `ForMathlib/` helper lemma feeding the boundary-cover construction; not a `## Main
results` entry, not named after a person/place, introduces no new structure. (Lit width run
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` — one-line `def` check is n/a. (For reference: the companion `def clampUnit`
at line 88 *is* a one-liner, but that is a separate declaration and out of scope here.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                            | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-----------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "C^1 function restricted to compact set is Lipschitz on that set"                               | yes  | C¹ ⟹ locally Lipschitz; locally-Lip + compact ⟹ Lipschitz      | Wikipedia "Lipschitz continuity"; ETSU primer; standard |
|  2 | WebSearch (general form)         | "continuously differentiable function locally Lipschitz mean value theorem"                    | yes  | C¹ ⟹ loc. Lip via bounded derivative + MVT; finite or Banach    | UC Davis Hunter notes; "The Unapologetic Mathematician" |
|  3 | WebSearch (named technique)      | "Lipschitz retraction onto convex set extend function globally Lipschitz composition"          | yes  | `f ↦ f ∘ ρ` with `ρ` a Lipschitz retraction extends/globalizes  | **Heinonen, *Lectures on Lipschitz Analysis*** — the globalize-by-retraction step is a *named standard technique*, always treated as trivial composition |
|  4 | ChatGPT MCP                      | standard-form + generality + "standalone lemma vs one-off helper" (3-part)                      | n/a  | —                                                               | MCP/Codex down (stdin error), per task warning — substituted by channels 1–3 + 9 |
|  5 | Local references                 | `.mathlib-quality/references/` for the project                                                  | n/a  | (directory absent)                                              | `projects/Chebotarev/.mathlib-quality/references/` does not exist |
|  6 | nLab                             | "Lipschitz map smooth function compact set bounded derivative"                                  | yes  | "functions with bounded derivative are Lipschitz"               | nLab *Lipschitz map* — confirms the atomic fact, no packaged composite |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                                                               | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | —                                                               | not an algebraic-geometry concept |
|  9 | MathOverflow / Math.SE           | (folded into #1–#3) Lipschitz-extension / retraction generality                                | yes  | retraction-composition is folklore; bounded-derivative ⟹ Lip   | corroborated across Heinonen, Lee (Princeton), arXiv:1207.0944 |
| 10 | recent arXiv (last 5y)           | "Lipschitz extension Lipschitz-free spaces retraction"                                          | yes  | `S` is Lipschitz-extendable iff a Lipschitz retraction onto `S` exists; operator `f ↦ f∘ρ` | arXiv:2601.03131, arXiv:1811.00603 — the retraction-composition operator is standard, never a standalone "C¹ ∘ cube-clamp" lemma |

The protocol passed: WebSearch ran 3 queries at distinct generality levels (specific / general /
named-technique); ChatGPT MCP recorded n/a with reason (tool down); local refs n/a (absent);
nLab checked (hit); Stacks/nCatLab n/a with reason; MathOverflow/arXiv checked (hit).

### Literature summary (Phase 3)

Concept identified as: a **composition of two standard facts** plus one standard *technique*:
  (a) "a `C¹` map is Lipschitz on a compact convex set" (consequence of the mean-value
      inequality / bounded derivative on a compact set), and
  (b) "precompose with a Lipschitz retraction onto that set to globalize" — a named technique
      in Lipschitz-extension theory (Heinonen).
Sources agree on the standard form: **yes**. (a) is universally stated; (b) is universally
treated as a *trivial composition* `f ↦ f ∘ ρ`, never elevated to a standalone packaged lemma.
Most general standard form: (a) holds for `C¹` (indeed `C¹`-on-a-convex-compact, or any
bounded-derivative map) between Banach spaces; (b) holds for any Lipschitz retraction `ρ` onto
any Lipschitz retract.
Generality dimensions where the literature varies:
  - domain: finite-dim `ℝⁿ` ↔ general Banach space — the most general is Banach.
  - regularity: `C¹` ↔ bounded-derivative ↔ locally-Lipschitz — most general is locally-Lipschitz.
  - target set: the unit cube `[0,1]ⁿ` ↔ any compact convex set ↔ any compact set (convexity
    only needed to pass `C¹` ⟹ Lipschitz; with locally-Lipschitz, any compact set works).
Disagreement with the literature: none. The literature simply does not package "C¹ ∘
cube-clamp ⟹ globally Lipschitz" as a single named statement — it is an instance of two
folklore facts.

---

### Generality analysis — `Chebotarev.exists_lipschitzWith_comp_clampUnit`

Literature-standard form (from Phase 3): for a Lipschitz retraction `ρ : X → S` onto a compact
convex `S` in a Banach space and a `C¹` (or locally-Lipschitz) `f`, `f ∘ ρ` is globally
Lipschitz. The retract `S` and the retraction `ρ` are general data, not fixed to `[0,1]ⁿ`.

| # | Parameter / hypothesis      | Current Lean form                       | Literature-standard form                 | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|------------------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | `ι κ` `[Fintype _]`, `ℝ`-pi | finite-dim'l real pi spaces (sup metric) | any normed/Banach spaces `E`, `F`         | yes                 | the engine `ContDiffOn.exists_lipschitzOnWith` is already Banach-general; the cube `Icc 0 1` and `clampUnit` are pi-specific, but the *principle* is space-agnostic |
| 2 | `hf : ContDiff ℝ 1 f`       | `C¹`                                     | locally Lipschitz (or bounded-deriv)      | yes                 | only `f`-Lipschitz-on-the-cube is used; `LocallyLipschitzOn` on the cube suffices, dropping `C¹` to locally-Lipschitz |
| 3 | clamp target `Icc 0 1`      | the unit cube `[0,1]^ι`                  | any compact convex set + a 1-Lip retract  | yes                 | `clampUnit` is hardwired to `[0,1]`; the general statement abstracts over the retraction onto an arbitrary compact (convex) retract |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (finite-dim pi, `C¹`, fixed unit cube).
Number of weakening opportunities found: 3.
Proposed (abstract) restatement, *if one were to generalise*:
```lean
-- "globalize a locally-Lipschitz-on-K map by a Lipschitz retraction onto K"
theorem LipschitzOnWith.comp_lipschitzWith_of_mapsTo {E F : Type*}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : E → F} {r : E → E} {K : Set E} {Kf Kr : ℝ≥0}
    (hf : LipschitzOnWith Kf f K) (hr : LipschitzWith Kr r) (hmaps : ∀ x, r x ∈ K) :
    LipschitzWith (Kf * Kr) (f ∘ r)
```
Cost of restatement: **CHEAP** as the *abstract globalization lemma* above (a few lines), but
that lemma is no longer "about the cube" — it is the generic retraction-composition fact, which
is itself a ≤3-call composition (see Phase 6). The cube-specialised packaging is the only thing
the project actually needs.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                          | Applies? | Proposed reformulation                          | Mathlib downstream |
|----|-----------------------------------------------------------------------------------|----------|--------------------------------------------------|--------------------|
|  1 | bundled-hypothesis preamble → typeclass/instance?                                 | no       | hypotheses are already mathlib typeclasses       | — |
|  2 | sequences/metric → filters/topological?                                           | no       | Lipschitz is the right metric-level notion here  | — |
|  3 | construct object → universal-property class?                                      | no       | nothing constructed; it is an `∃ M` bound        | — |
|  4 | set-with-predicate → bundled substructure?                                        | no       | no substructure involved                         | — |
|  5 | field/metric-specific → weaken typeclass hierarchy (modules/(pseudo)metric)?      | yes      | abstract over `E F` Banach/pseudometric + generic retraction (Phase 4b restatement) | composes with `LipschitzOnWith.comp` / `LipschitzWith.comp` everywhere |
|  6 | 1-categorical → higher-categorical?                                               | no       | n/a                                              | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                    | no       | the `ℝ`/cube here is essential to `projIcc`      | — |

### Modern-idiom verdict (Phase 4c)
Modern idiom available: **yes** (row 5) — but the idiomatic move is to *drop the cube/clampUnit
specialisation entirely* in favour of the generic "retraction-composition globalizes Lipschitz"
lemma. Crucially, that generic lemma is itself a ≤3-call composition of existing mathlib
primitives (Phase 6), so the modern idiom points *toward NO-composable*, not toward shipping a
new packaged lemma. Real mathematical improvement: none beyond what `LipschitzWith.comp` /
`LipschitzOnWith.comp` already provide.

---

### Diamond / defeq risk — Phase 4.5
n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search
paths). [Note: the dependency `def clampUnit` is a separate decl; its risk is out of scope.]

---

### Mathlib search-status: `Chebotarev.exists_lipschitzWith_comp_clampUnit`

[A] Lean-Finder       n/a (deferred tool not available in this env)
[B] Loogle            n/a (deferred tool not available); substituted by direct mathlib-src grep [D]
[C] LeanSearch        WebSearch against `leanprover-community.github.io/mathlib4_docs` for
                       "LipschitzOnWith extend whole space retraction projIcc clamp" → no exact hit;
                       surfaced `Lipschitz.lean`, `FiniteDimension.lean` (the Whitney-type extension)
[D] Grep mathlib src  `exists_lipschitzOnWith_of_compact`, `ContDiff.locallyLipschitz`,
                       `ContDiffOn.exists_lipschitzOnWith`, `projIcc`+Lipschitz, `def …[Cc]lamp`,
                       `comp_lipschitzWith`, `IccExtend`+Lipschitz, `LipschitzWith.weaken/comp/edist_le_mul`
                       → all building blocks FOUND; no packaged "C¹ ∘ cube-clamp ⟹ global Lipschitz"
[E] Name pattern      grep for `clampUnit`, `comp_clampUnit`, `clamp_comp` in mathlib → none

Searched for both:
  - the user's current form ("`C¹` ∘ unit-cube-clamp globally Lipschitz") — **not in mathlib**;
  - the literature-standard form:
      · "C¹ on compact convex ⟹ Lipschitz" → **FOUND** as
        `ContDiffOn.exists_lipschitzOnWith` (`Mathlib/Analysis/Calculus/ContDiff/RCLike.lean:148`),
        and the unbundled pieces `ContDiff.locallyLipschitz` (`…:143`),
        `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`
        (`Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean:58`);
      · "1-Lipschitz clamp onto Icc" → **FOUND** as `LipschitzWith.projIcc`
        (`Mathlib/Topology/MetricSpace/Lipschitz.lean:199`);
      · generic "retraction-composition globalizes" packaged lemma → **NOT in mathlib** (no
        `LipschitzOnWith.comp_lipschitzWith`; the closest is `LipschitzOnWith.comp` at
        `Mathlib/Topology/EMetricSpace/Lipschitz.lean:328` plus `Set.MapsTo.lipschitzOnWith_iff_restrict`).

Concluded: **"found building blocks; composition would yield our form."** Mathlib has the heavy
mathematical content (`ContDiffOn.exists_lipschitzOnWith`) and every glue primitive
(`LipschitzWith.projIcc`, `LipschitzOnWith.comp`, `LipschitzWith.comp/weaken/edist_le_mul`,
`convex_Icc`, `isCompact_Icc`). It does NOT have the exact `clampUnit`-specialised packaging,
nor the generic retraction-globalization lemma.

---

### Call sites — `Chebotarev.exists_lipschitzWith_comp_clampUnit`

Internal use count: **2** (within the project; NOT counting the declaring file's own docstring).
External-to-file callers: **0 distinct files**. Both uses are *inside the declaring file itself*
(`NormLeOneLipschitz.lean`).

| Caller file:line                       | Usage pattern (one-line excerpt)                                              |
|----------------------------------------|-------------------------------------------------------------------------------|
| NormLeOneLipschitz.lean:298            | `obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)` |
| NormLeOneLipschitz.lean:300            | `exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))` |
| NormLeOneLipschitz.lean:292            | (docstring mention only — not a call)                                          |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none found) — the only consumers are the two face-map Lipschitz proofs above.

Composability signal: **K = 2 internal uses, both confined to the single declaring file, 0
external callers.** Per the call-sites table this is a private-helper / wrong-abstraction signal
leaning toward NO-composable — it exists purely to apply the same 4-line composition twice
(once per face-map family) inside one construction.

---

### Composition check (Phase 6)

Can `exists_lipschitzWith_comp_clampUnit` be derived from mathlib in ≤3 chained calls?

Attempt 1 (mirror the source proof, via the bundled engine):
```lean
example {ι κ : Type*} [Fintype ι] [Fintype κ] {f : (ι → ℝ) → κ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι) := by
  obtain ⟨M, hM⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
  exact ⟨M, fun c d ↦ (hM (clampUnit_mem_Icc ι c) (clampUnit_mem_Icc ι d)).trans <| by
    simpa using (lipschitzWith_clampUnit ι).edist_le_mul c d⟩   -- + a `gcongr`/`mul_one`
```
  - Mathlib decls used: `ContDiffOn.exists_lipschitzOnWith`, `convex_Icc`, `isCompact_Icc`,
    `LipschitzWith.edist_le_mul` (and the project's own `clampUnit_mem_Icc`,
    `lipschitzWith_clampUnit`).
  - Result: **succeeds** — but the last step is a genuine `edist`-bookkeeping glue
    (`.trans` + `gcongr` + `mul_one`), not a pure `f (g x)` one-liner. The "1-Lipschitz clamp
    lands in the cube, so the on-cube bound transfers globally" step is real (small) reasoning.
  - Notes: this is exactly the source proof with `ContDiff.locallyLipschitz` +
    `…exists_lipschitzOnWith_of_compact` folded into the single bundled
    `ContDiffOn.exists_lipschitzOnWith`. The mathematical heavy lifting is one mathlib call.

Attempt 2 (if a generic globalization lemma existed):
```lean
-- with the hypothetical LipschitzOnWith.comp_lipschitzWith_of_mapsTo (Phase 4b):
example … := let ⟨M, hM⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
  ⟨M * 1, hM.comp_lipschitzWith_of_mapsTo (lipschitzWith_clampUnit ι) (clampUnit_mem_Icc ι)⟩
```
  - This would be a clean 2-call composition — but `LipschitzOnWith.comp_lipschitzWith_of_mapsTo`
    is itself not in mathlib (closest: `LipschitzOnWith.comp` + `Set.MapsTo.lipschitzOnWith_iff_restrict`).

Conclusion: **COMPOSABLE (borderline).** The result follows from `ContDiffOn.exists_lipschitzOnWith`
plus the 1-Lipschitz clamp landing in the cube, glued by a short `edist` `.trans`/`gcongr` step
(≈3 mathlib calls + 1 line of bookkeeping). It is not a pristine `Foo.bar (Baz.qux h)` one-liner,
but it is squarely "building blocks compose to give it" rather than a substantial new proof — and
the *only* part not already in mathlib (the generic retraction-globalization) is itself a ≤3-call
composition.

---

## Verdict: `Chebotarev.exists_lipschitzWith_comp_clampUnit`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the statement = two folklore facts ("C¹ on compact convex ⟹
  Lipschitz" + "precompose with a Lipschitz retraction to globalize"); the globalization is a
  *named standard technique* (Heinonen) always treated as trivial composition, never packaged.
- Generality analysis (Phase 4): STRICTLY NARROWER (finite-dim pi, `C¹`, fixed unit cube); the
  idiomatic generalisation is the generic retraction-globalization lemma, which is itself
  composable — so 4c points toward NO-composable, not toward a new packaged lemma.
- Mathlib search (Phase 5): "found building blocks" — `ContDiffOn.exists_lipschitzOnWith`
  (`Mathlib/Analysis/Calculus/ContDiff/RCLike.lean:148`) supplies the entire mathematical
  content; `LipschitzWith.projIcc`, `LipschitzOnWith.comp`, `convex_Icc`, `isCompact_Icc`,
  `LipschitzWith.edist_le_mul/weaken` supply the glue. No `clampUnit`-packaged or generic
  globalization lemma exists.
- Composition check (Phase 6): COMPOSABLE (≈3 mathlib calls + one short `edist` glue step).

**Rationale:**

The mathematical substance of this lemma — "a `C¹` map is Lipschitz on the compact convex unit
cube" — is *exactly* `ContDiffOn.exists_lipschitzOnWith`, already in mathlib (added precisely so
downstream code does not re-derive `C¹`-on-compact ⟹ Lipschitz). What the project's lemma adds on
top is the cube-clamp `clampUnit` and the observation that precomposing with a 1-Lipschitz
retraction onto the cube turns the on-cube bound into a *global* bound. The literature is
unambiguous that this globalization-by-Lipschitz-retraction is a standard, trivial composition
(`f ↦ f ∘ ρ`, Heinonen's *Lectures on Lipschitz Analysis*; arXiv:2601.03131; arXiv:1207.0944),
never elevated to a named lemma. Concretely, the source proof is four lines and reduces to one
mathlib call (`ContDiffOn.exists_lipschitzOnWith`, replacing the project's two-step
`locallyLipschitz` + `exists_lipschitzOnWith_of_compact`) followed by a short `edist` `.trans` /
`gcongr` step using that `clampUnit` is `1`-Lipschitz (`LipschitzWith.projIcc`) and lands in the
cube. That is a composition of existing mathlib primitives, not new content.

The call-sites evidence reinforces NO: the lemma has **2 uses, both inside its own declaring
file**, **0 external callers**, and no inline re-derivation elsewhere — a private helper that
exists only to apply the same composition twice (once for `faceMapZero`, once for `faceMapSide`)
within the frontier-cover construction. It is the right *local* abstraction for this file, but it
is not a mathlib-shaped contribution: the cube-clamp specialisation is project-specific, and the
genuinely reusable kernel (`C¹`-on-compact ⟹ Lipschitz) is already upstream.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the lemma is a 2–3-call composition.

Mathlib building blocks (qualified names + paths):
- `ContDiffOn.exists_lipschitzOnWith` — `Mathlib/Analysis/Calculus/ContDiff/RCLike.lean:148`
  (`C¹`-on-convex-compact ⟹ `∃ K, LipschitzOnWith K f s`); the engine.
- `LipschitzWith.projIcc` — `Mathlib/Topology/MetricSpace/Lipschitz.lean:199` (the 1-Lipschitz
  coordinate clamp underlying `clampUnit` / `lipschitzWith_clampUnit`).
- `LipschitzWith.edist_le_mul` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:138`;
  `convex_Icc` — `Mathlib/Analysis/Convex/Basic.lean:254`; `isCompact_Icc` (order-topology).
- (project-local glue already present: `clampUnit_mem_Icc`, `lipschitzWith_clampUnit`.)

Composition sketch (≤3 mathlib calls + one glue line):
```lean
obtain ⟨M, hM⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
exact ⟨M, fun c d ↦ (hM (clampUnit_mem_Icc ι c) (clampUnit_mem_Icc ι d)).trans <| by
  simpa [mul_one] using (lipschitzWith_clampUnit ι).edist_le_mul c d⟩
```

Call sites in the project (from Phase 6.0): **K = 2**, both in `NormLeOneLipschitz.lean` (lines
298, 300), 0 external.

Refactor plan (this is a refactor/keep-local recommendation, NOT a delete-from-the-library
recommendation — `main` keeps the helper; the point is it should not be PR'd to mathlib):
- Do **not** open a mathlib PR for this lemma. The reusable kernel is already mathlib
  (`ContDiffOn.exists_lipschitzOnWith`); the `clampUnit` packaging is project-specific.
- If a cleanup pass wants to *golf* the proof in-place: replace the current
  `hf.locallyLipschitz.locallyLipschitzOn …` + `…exists_lipschitzOnWith_of_compact isCompact_Icc`
  two-step with the single `hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1)
  isCompact_Icc` call (the sketch above). Statement unchanged; both call sites (298, 300) are
  unaffected since the lemma's type is identical.
- Optional upstreaming, separated from this decl: if mathlib ever wants the *generic*
  "Lipschitz-retraction composition globalizes a `LipschitzOnWith`" lemma
  (`LipschitzOnWith.comp_lipschitzWith_of_mapsTo`, Phase 4b), that is a legitimate small mathlib
  addition on its own — but it is a different, cube-free statement, and even it is a ≤3-call
  composition of `LipschitzOnWith.comp` + `Set.MapsTo.lipschitzOnWith_iff_restrict`.

Next action: keep `exists_lipschitzWith_comp_clampUnit` project-local (it is fine as a
`ForMathlib/` *internal* helper); optionally golf its proof to the single-call form above. Do not
queue it for a mathlib PR.

---

## Next step

Keep the lemma project-local; do not PR to mathlib. The mathematical content is
`ContDiffOn.exists_lipschitzOnWith` (already upstream) composed with the 1-Lipschitz cube clamp
(`LipschitzWith.projIcc`). Optionally golf the proof to the single-engine-call form. If desired,
upstream the *generic* retraction-globalization lemma separately — but that too is a ≤3-call
composition, not this cube-specialised packaging.
